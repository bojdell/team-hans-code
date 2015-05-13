#include <std.h>
#include <log.h>
#include <clk.h>
#include <gbl.h>
#include <bcache.h>

#include <mem.h> // MEM_alloc calls
#include <que.h> // QUE functions
#include <sem.h> // Semaphore functions
#include <sys.h> 
#include <tsk.h> // TASK functions
#include <math.h> 
#include <stdio.h> 
#include <stdlib.h>
#include <string.h>
#include <c6x.h> // register defines


#include "projectinclude.h"
#include "c67fastMath.h" // sinsp,cossp, tansp
#include "evmomapl138.h"
#include "evmomapl138_i2c.h"
#include "evmomapl138_timer.h"
#include "evmomapl138_led.h"
#include "evmomapl138_dip.h"
#include "evmomapl138_gpio.h"
#include "evmomapl138_vpif.h"
#include "evmomapl138_spi.h"
#include "COECSL_edma3.h"
#include "COECSL_mcbsp.h"
#include "COECSL_registers.h"

#include "mcbsp_com.h"
#include "ColorVision.h"
#include "ColorLCD.h"
#include "sharedmem.h"
#include "LCDprintf.h"
#include "ladar.h"
#include "xy.h"
#include "MatrixMath.h"

#define FEETINONEMETER 3.28083989501312

#define GOLF_BALL_THRESH	5
#define BLUE_BALL_COL		6
#define ORANGE_BALL_COL		-25
#define TURN_THRESH			0.5		// how closely we need to be angled towards a ball before we start going towards it
#define BALL_PICKUP_DIST	0.25		// how far we overshoot a ball (in tiles) to make sure we've picked it up
#define FRONT_ERROR_THRESH	2650
#define COURSE_BOUND_TOP	12
#define COURSE_BOUND_BOTTOM	0
#define COURSE_BOUND_LEFT	-6
#define COURSE_BOUND_RIGHT	6
#define COURSE_BOUND_OFFSET 1
#define BALL_DROPOFF_TIMER  1000

extern EDMA3_CCRL_Regs *EDMA3_0_Regs;

volatile uint32_t index;

// test variables
extern float enc1;  // Left motor encoder
extern float enc2;  // Right motor encoder
extern float enc3;
extern float enc4;
extern float adcA0;  // ADC A0 - Gyro_X -400deg/s to 400deg/s  Pitch
extern float adcB0;  // ADC B0 - External ADC Ch4 (no protection circuit)
extern float adcA1;  // ADC A1 - Gyro_4X -100deg/s to 100deg/s  Pitch
extern float adcB1;  // ADC B1 - External ADC Ch1
extern float adcA2;  // ADC A2 -	Gyro_4Z -100deg/s to 100deg/s  Yaw
extern float adcB2;  // ADC B2 - External ADC Ch2
extern float adcA3;  // ADC A3 - Gyro_Z -400deg/s to 400 deg/s  Yaw
extern float adcB3;  // ADC B3 - External ADC Ch3
extern float adcA4;  // ADC A4 - Analog IR1
extern float adcB4;  // ADC B4 - USONIC1
extern float adcA5;  // ADC A5 -	Analog IR2
extern float adcB5;  // ADC B5 - USONIC2
extern float adcA6;  // ADC A6 - Analog IR3
extern float adcA7;  // ADC A7 - Analog IR4
extern float compass;
extern float switchstate;

float vref = 2;
float turn = 0;

int tskcount = 0;
char fromLinuxstring[LINUX_COMSIZE + 2];
char toLinuxstring[LINUX_COMSIZE + 2];

float LVvalue1 = 0;
float LVvalue2 = 0;
int new_LV_data = 0;

int newnavdata = 0;
float rightVref = 1.3;
float newturn = 0;
unsigned char whichAvoid = 0;

extern sharedmemstruct *ptrshrdmem;

float x_pred[3][1] = {{0},{0},{0}};					// predicted state

//more kalman vars
float B[3][2] = {{1,0},{1,0},{0,1}};			// control input model
float u[2][1] = {{0},{0}};			// control input in terms of velocity and angular velocity
float Bu[3][1] = {{0},{0},{0}};	// matrix multiplication of B and u
float z[3][1];							// state measurement
float eye3[3][3] = {{1,0,0},{0,1,0},{0,0,1}};	// 3x3 identity matrix
float K[3][3] = {{1,0,0},{0,1,0},{0,0,1}};		// optimal Kalman gain
#define ProcUncert 0.0001
#define CovScalar 10
float Q[3][3] = {{ProcUncert,0,ProcUncert/CovScalar},
				 {0,ProcUncert,ProcUncert/CovScalar},
				 {ProcUncert/CovScalar,ProcUncert/CovScalar,ProcUncert}};	// process noise (covariance of encoders and gyro)
#define MeasUncert 1
float R[3][3] = {{MeasUncert,0,MeasUncert/CovScalar},
				 {0,MeasUncert,MeasUncert/CovScalar},
				 {MeasUncert/CovScalar,MeasUncert/CovScalar,MeasUncert}};	// measurement noise (covariance of LADAR)
float S[3][3] = {{1,0,0},{0,1,0},{0,0,1}};	// innovation covariance
float S_inv[3][3] = {{1,0,0},{0,1,0},{0,0,1}};	// innovation covariance matrix inverse
float P_pred[3][3] = {{1,0,0},{0,1,0},{0,0,1}};	// predicted covariance (measure of uncertainty for current position)
float temp_3x3[3][3];				// intermediate storage
float temp_3x1[3][1];				// intermediate storage
float ytilde[3][1];					// difference between predictions

// deadreckoning
float vel1 = 0,vel2 = 0;
float vel1old = 0,vel2old = 0;
float enc1old = 0,enc2old = 0;

// SETTLETIME should be an even number and divisible by 3
#define SETTLETIME 6000
int settlegyro = 0;
float gyro_zero = 0;
float gyro_angle = 0;
float old_gyro = 0;
float gyro_drift = 0;
float gyro = 0;
int gyro_degrees = 0;
float gyro_radians = 0.0;
float gyro_x = 0,gyro_y = 0;
float gyro4x_gain = 1;

int statePos = 0;	// index into robotdest
int robotdestSize = 8;	// number of positions to use out of robotdest
pose robotdest[12];	// array of waypoints for the robot
pose ballReturnPoint;



extern float newLADARdistance[LADAR_MAX_DATA_SIZE];  //in mm
extern float newLADARangle[LADAR_MAX_DATA_SIZE];		// in degrees
float LADARdistance[LADAR_MAX_DATA_SIZE];
float LADARangle[LADAR_MAX_DATA_SIZE];
extern pose ROBOTps;
extern pose LADARps;
extern float newLADARdataX[LADAR_MAX_DATA_SIZE];
extern float newLADARdataY[LADAR_MAX_DATA_SIZE];
float LADARdataX[LADAR_MAX_DATA_SIZE];
float LADARdataY[LADAR_MAX_DATA_SIZE];
extern int newLADARdata;

// Optitrack Variables
int trackableIDerror = 0;
int firstdata = 1;
volatile int new_optitrack = 0;
volatile float previous_frame = -1;
int frame_error = 0;
volatile float Optitrackdata[OPTITRACKDATASIZE];
pose OPTITRACKps;
float temp_theta = 0.0;
float tempOPTITRACK_theta = 0.0;
volatile int temp_trackableID = -1;
int trackableID = -1;
int errorcheck = 1;

//Wall following
float kpright = 0.004;
float kpfront = 0.003;
float kpvision = 0.069;
float refright = 350;
float frontturnvel = 0.2;
float turnsat = 2;
float corner_error_threshold = 2750;
char is_avoiding_obstacle = 0;
float xVal = 0;
float yVal = 0;


// for determining distance
float distance_inches = 0.0;
float distance_second = 0.019174;
float distance_first = 2.1923;
float distance_zero = 82.503;

// Ball detection
extern unsigned char new_vision_data;
extern int blue_rbar, blue_cbar, blueNumPixels;
extern int green_rbar, green_cbar, greenNumPixels;
extern int orange_rbar, orange_cbar, orangeNumPixels;
int local_blue_rbar = 0;
int local_blue_cbar = 0;
int local_blueNumPixels = 0;
int local_green_rbar, local_green_cbar, local_greenNumPixels;
int local_orange_rbar = 0;
int local_orange_cbar = 0;
int local_orangeNumPixels = 0;
int ball_following = 0;
float kp_ball = 0.02;
float minimum_ball_speed = 0.2;
//float kp_ball_turn = 0.25;
float kp_ball_turn = 0.05;
float ballTurnError = 0;
char ball_mapped = 0;
float endLocX = 0;
float endLocY = 0;
int case2ctr = 0;
char ball_state = 0;
float blueServo = 13.0;
float orangeServo = 4.0;
char ballColor = 0;
float thetaDiff = 0;
float initialTheta = 0;

// Object following
float slope = 0;
float slopeThreshold = 40;
float hitX = 0;
float hitY = 0;
char newObs = 0; // 1 = newObj found, 2 = lower flag when departed from goal line, 3 = raise flag when re-entering goal line
char prevNewObs = 1;

// audio stuff
char playAudio = 0;
char audioClip[256];

//Labview ball location
int newBall = 0;
float ballLocationX = 0;
float ballLocationY = 0;

// ball dropoff
long timeCheat = 0;

pose UpdateOptitrackStates(pose localROBOTps, int * flag);


void ComWithLinux(void) {

	int i = 0;
	TSK_sleep(100);

	while(1) {

		BCACHE_inv((void *)ptrshrdmem,sizeof(sharedmemstruct),EDMA3_CACHE_WAIT);
		
		if (GET_DATA_FROM_LINUX) {

			if (newnavdata == 0) {
				rightVref = ptrshrdmem->Floats_to_DSP[0];
				newturn = ptrshrdmem->Floats_to_DSP[1];
				newnavdata = 1;
			}

			CLR_DATA_FROM_LINUX;

		}

		if (GET_LVDATA_FROM_LINUX) {

			if (ptrshrdmem->DSPRec_size > 256) ptrshrdmem->DSPRec_size = 256;
				for (i=0;i<ptrshrdmem->DSPRec_size;i++) {
					fromLinuxstring[i] = ptrshrdmem->DSPRec_buf[i];
				}
				fromLinuxstring[i] = '\0';

				if (new_LV_data == 0) {
					sscanf(fromLinuxstring,"%f%f",&LVvalue1,&LVvalue2);
					new_LV_data = 1;
				}

			CLR_LVDATA_FROM_LINUX;

		}

		if ((tskcount%6)==0) {
			if (GET_LVDATA_TO_LINUX) {

				// Default
				//ptrshrdmem->DSPSend_size = sprintf(toLinuxstring,"1.0 1.0 1.0 1.0");
				// you would do something like this
				ptrshrdmem->DSPSend_size = sprintf(toLinuxstring,"%.1f %.1f %.1f %.1f %.1f %.1f %d %d", ROBOTps.x, ROBOTps.y, hitX, hitY, ballLocationX, ballLocationY, ballColor, newBall);

				if(newBall) //If just sent ball location, don't want to send again
				{
					newBall =0;
				}

				for (i=0;i<ptrshrdmem->DSPSend_size;i++) {
					ptrshrdmem->DSPSend_buf[i] = toLinuxstring[i];
				}

				// Flush or write back source
				BCACHE_wb((void *)ptrshrdmem,sizeof(sharedmemstruct),EDMA3_CACHE_WAIT);

				CLR_LVDATA_TO_LINUX;

			}
		}
		
		if (GET_DATAFORFILE_TO_LINUX) {

//			// First make sure all scratch elements are zero
//			for (i=0;i<500;i++) {
//				ptrshrdmem->scratch[i] = 0;
//			}
//			// Write LADARdataX to scratch
//			for (i=0;i<228;i++) {
//				ptrshrdmem->scratch[i] = LADARdataX[i];
//			}
//			// Write LADARdataY to scratch
//			for (i=0;i<228;i++) {
//				ptrshrdmem->scratch[228+i] = LADARdataY[i];
//			}
//			// Flush or write back source
//			BCACHE_wb((void *)ptrshrdmem,sizeof(sharedmemstruct),EDMA3_CACHE_WAIT);
//			CLR_DATAFORFILE_TO_LINUX;

			// This is an example write to scratch
			// The Linux program SaveScratchToFile can be used to write the
			// ptrshrdmem->scratch[0-499] memory to a .txt file.
//			for (i=100;i<300;i++) {
//				ptrshrdmem->scratch[i] = (float)i;
//			}
			// fist char = 'opcode': b = bwang.sh, x = robotspeak.sh followed by string to speak
			if(playAudio) {
				strcpy((char *)(ptrshrdmem->scratch), audioClip);

				// Flush or write back source
				BCACHE_wb((void *)ptrshrdmem,sizeof(sharedmemstruct),EDMA3_CACHE_WAIT);

				playAudio = 0;
				CLR_DATAFORFILE_TO_LINUX;
			}

		}

		tskcount++;
		TSK_sleep(40);
	}


}

unsigned char onLeftOfRobot(float targetX, float targetY)
{
	xVal = targetX*cosf(ROBOTps.theta) + targetY*sinf(ROBOTps.theta) - ROBOTps.x*cosf(ROBOTps.theta) - ROBOTps.y*sinf(ROBOTps.theta);
	yVal = targetX*sinf(ROBOTps.theta) + targetY*cosf(ROBOTps.theta) + ROBOTps.x*sinf(ROBOTps.theta) - ROBOTps.y*cosf(ROBOTps.theta);

	if(yVal > 0 && (fabsf(xVal) < 1))
		return 1;

	return 0;

}

void findSlope(float curX, float curY, float destX, float destY)
{
	slope = (destY-curY)/(destX-curX);
}

unsigned char lineCheck(float curX, float curY, float destX, float destY)
{
	if (fabsf((destY-curY)/(destX-curX)-slope) < slopeThreshold)
	{
		return 1;
	}
	return 0;
}

// returns distance between 2 points
float getDist(float x1, float y1, float x2, float y2) {
	float dx = x2 - x1;
	float dy = y2 - y1;
	return sqrtf( dx*dx + dy*dy );
}

// returns angular distance from theta1 to theta2
float angularDiff(float theta1, float theta2) {
	if(theta2 < theta1)
		theta2 += 2*PI;
	return theta2 - theta1;
}

// maps a ball
void mapBall(float dist_tiles) {
	float dx = BALL_PICKUP_DIST * cosf(ROBOTps.theta);
	float dy = BALL_PICKUP_DIST * sinf(ROBOTps.theta);
	ballLocationX = ROBOTps.x + dist_tiles * cosf(ROBOTps.theta);
	ballLocationY = ROBOTps.y + dist_tiles * sinf(ROBOTps.theta);

	// get initial endpoint
	endLocX = ballLocationX + dx;
	endLocY = ballLocationY + dy;

	// clip coordinates outside the course boundaries
	if(endLocX > COURSE_BOUND_RIGHT) {
		dx = COURSE_BOUND_RIGHT - COURSE_BOUND_OFFSET - ballLocationX;
		dy = dx * tanf(ROBOTps.theta);
	}
	else if(endLocX < COURSE_BOUND_LEFT) {
		dx = COURSE_BOUND_LEFT + COURSE_BOUND_OFFSET - ballLocationX;
		dy = dx * tanf(ROBOTps.theta);
	}

	if(endLocY > COURSE_BOUND_TOP) {
		dy = COURSE_BOUND_TOP - COURSE_BOUND_OFFSET - ballLocationY;
		dx = dy / tanf(ROBOTps.theta);
	}
	else if(endLocY < COURSE_BOUND_BOTTOM) {
		dy = COURSE_BOUND_BOTTOM + COURSE_BOUND_OFFSET - ballLocationY;
		dx = dy / tanf(ROBOTps.theta);
	}

	// clip endpoint if necessary
	endLocX = ballLocationX + dx;
	endLocY = ballLocationY + dy;
}

/*
 *  ======== main ========
 */
Void main()
{

	int i = 0;

	// unlock the system config registers.
	SYSCONFIG->KICKR[0] = KICK0R_UNLOCK;
	SYSCONFIG->KICKR[1] = KICK1R_UNLOCK;

	SYSCONFIG1->PUPD_SEL |= 0x10000000;  // change pin group 28 to pullup for GP7[12/13] (LCD switches)

	// Initially set McBSP1 pins as GPIO ins
	CLRBIT(SYSCONFIG->PINMUX[1], 0xFFFFFFFF);
	SETBIT(SYSCONFIG->PINMUX[1], 0x88888880);  // This is enabling the McBSP1 pins

	CLRBIT(SYSCONFIG->PINMUX[16], 0xFFFF0000);
	SETBIT(SYSCONFIG->PINMUX[16], 0x88880000);  // setup GP7.8 through GP7.13 
	CLRBIT(SYSCONFIG->PINMUX[17], 0x000000FF);
	SETBIT(SYSCONFIG->PINMUX[17], 0x00000088);  // setup GP7.8 through GP7.13


	//Rick added for LCD DMA flagging test
	GPIO_setDir(GPIO_BANK0, GPIO_PIN8, GPIO_OUTPUT);
	GPIO_setOutput(GPIO_BANK0, GPIO_PIN8, OUTPUT_HIGH);

	GPIO_setDir(GPIO_BANK0, GPIO_PIN0, GPIO_INPUT);
	GPIO_setDir(GPIO_BANK0, GPIO_PIN1, GPIO_INPUT);
	GPIO_setDir(GPIO_BANK0, GPIO_PIN2, GPIO_INPUT);
	GPIO_setDir(GPIO_BANK0, GPIO_PIN3, GPIO_INPUT);
	GPIO_setDir(GPIO_BANK0, GPIO_PIN4, GPIO_INPUT);
	GPIO_setDir(GPIO_BANK0, GPIO_PIN5, GPIO_INPUT);  
	GPIO_setDir(GPIO_BANK0, GPIO_PIN6, GPIO_INPUT);

	GPIO_setDir(GPIO_BANK7, GPIO_PIN8, GPIO_OUTPUT);
	GPIO_setDir(GPIO_BANK7, GPIO_PIN9, GPIO_OUTPUT);
	GPIO_setDir(GPIO_BANK7, GPIO_PIN10, GPIO_OUTPUT);
	GPIO_setDir(GPIO_BANK7, GPIO_PIN11, GPIO_OUTPUT);
	GPIO_setDir(GPIO_BANK7, GPIO_PIN12, GPIO_INPUT);
	GPIO_setDir(GPIO_BANK7, GPIO_PIN13, GPIO_INPUT); 

	GPIO_setOutput(GPIO_BANK7, GPIO_PIN8, OUTPUT_HIGH);  
	GPIO_setOutput(GPIO_BANK7, GPIO_PIN9, OUTPUT_HIGH);
	GPIO_setOutput(GPIO_BANK7, GPIO_PIN10, OUTPUT_HIGH);
	GPIO_setOutput(GPIO_BANK7, GPIO_PIN11, OUTPUT_HIGH);  

	CLRBIT(SYSCONFIG->PINMUX[13], 0xFFFFFFFF);
	SETBIT(SYSCONFIG->PINMUX[13], 0x88888811); //Set GPIO 6.8-13 to GPIOs and IMPORTANT Sets GP6[15] to /RESETOUT used by PHY, GP6[14] CLKOUT appears unconnected

	#warn GP6.15 is also connected to CAMERA RESET This is a Bug in my board design Need to change Camera Reset to different IO.

	GPIO_setDir(GPIO_BANK6, GPIO_PIN8, GPIO_OUTPUT);
	GPIO_setDir(GPIO_BANK6, GPIO_PIN9, GPIO_OUTPUT);
	GPIO_setDir(GPIO_BANK6, GPIO_PIN10, GPIO_OUTPUT);
	GPIO_setDir(GPIO_BANK6, GPIO_PIN11, GPIO_OUTPUT);
	GPIO_setDir(GPIO_BANK6, GPIO_PIN12, GPIO_OUTPUT);
	GPIO_setDir(GPIO_BANK6, GPIO_PIN13, GPIO_INPUT);   


   // on power up wait until Linux has initialized Timer1
	while ((T1_TGCR & 0x7) != 0x7) {
	  for (index=0;index<50000;index++) {}  // small delay before checking again

	}

	USTIMER_init();
	
	// Turn on McBSP1
	EVMOMAPL138_lpscTransition(PSC1, DOMAIN0, LPSC_MCBSP1, PSC_ENABLE);

    // If Linux has already booted It sets a flag so no need to delay
    if ( GET_ISLINUX_BOOTED == 0) {
    	USTIMER_delay(4*DELAY_1_SEC);  // delay allowing Linux to partially boot before continuing with DSP code
    }
	   
	// init the us timer and i2c for all to use.
	I2C_init(I2C0, I2C_CLK_100K);
	init_ColorVision();	
	init_LCD_mem(); // added rick

	EVTCLR0 = 0xFFFFFFFF;
	EVTCLR1 = 0xFFFFFFFF;
	EVTCLR2 = 0xFFFFFFFF;
	EVTCLR3 = 0xFFFFFFFF;	

	init_DMA();
	init_McBSP();

	init_LADAR();

	CLRBIT(SYSCONFIG->PINMUX[1], 0xFFFFFFFF);
	SETBIT(SYSCONFIG->PINMUX[1], 0x22222220);  // This is enabling the McBSP1 pins

	CLRBIT(SYSCONFIG->PINMUX[5], 0x00FF0FFF);
	SETBIT(SYSCONFIG->PINMUX[5], 0x00110111);  // This is enabling SPI pins

	CLRBIT(SYSCONFIG->PINMUX[16], 0xFFFF0000);
	SETBIT(SYSCONFIG->PINMUX[16], 0x88880000);  // setup GP7.8 through GP7.13 
	CLRBIT(SYSCONFIG->PINMUX[17], 0x000000FF);
	SETBIT(SYSCONFIG->PINMUX[17], 0x00000088);  // setup GP7.8 through GP7.13

	init_LCD();
    
	LADARps.x = 3.5/12; // 3.5/12 for front mounting
	LADARps.y = 0;
	LADARps.theta = 1;  // not inverted

	OPTITRACKps.x = 0;
	OPTITRACKps.y = 0;
	OPTITRACKps.theta = 0;

	for(i = 0;i<LADAR_MAX_DATA_SIZE;i++)
	{ LADARdistance[i] = LADAR_MAX_READING; } //initialize all readings to max value.

	// ROBOTps will be updated by Optitrack during gyro calibration
	// TODO: specify the starting position of the robot
	ROBOTps.x = 0;			//the estimate in array form (useful for matrix operations)
	ROBOTps.y = 0;
	ROBOTps.theta = 0;  // was -PI: need to flip OT ground plane to fix this
	x_pred[0][0] = ROBOTps.x; //estimate in structure form (useful elsewhere)
	x_pred[1][0] = ROBOTps.y;
	x_pred[2][0] = ROBOTps.theta;

	// TODO: defined destinations that moves the robot around and outside the course
	robotdest[0].x = -5;	robotdest[0].y = -3; // Point 1
	robotdest[1].x = 0;		robotdest[1].y = -1; // Home base (enter course)
	robotdest[2].x = 3;		robotdest[2].y = 7; // Point 2
	robotdest[3].x = -3;	robotdest[3].y = 7; // Point 3
	robotdest[4].x = 0;		robotdest[4].y = -1; // Home base (exit course)
	robotdest[5].x = 5;		robotdest[5].y = -3; // Point 4
	robotdest[6].x = 0;		robotdest[6].y = -1; // Home base (enter course)
	robotdest[7].x = 0;		robotdest[7].y = 11; // Point 5
	robotdest[8].x = 0;		robotdest[8].y = -1; // Home base (enter course)
	robotdest[9].x = -2;		robotdest[9].y = -4; // blue chute
	robotdest[10].x = 2;		robotdest[10].y = -4; // orange chute

	// flag pins
	GPIO_setDir(IMAGE_TO_LINUX_BANK, IMAGE_TO_LINUX_FLAG, GPIO_OUTPUT);
	GPIO_setDir(OPTITRACKDATA_FROM_LINUX_BANK, OPTITRACKDATA_FROM_LINUX_FLAG, GPIO_OUTPUT);
	GPIO_setDir(DATA_TO_LINUX_BANK, DATA_TO_LINUX_FLAG, GPIO_OUTPUT);
	GPIO_setDir(DATA_FROM_LINUX_BANK, DATA_FROM_LINUX_FLAG, GPIO_OUTPUT);
	GPIO_setDir(DATAFORFILE_TO_LINUX_BANK, DATAFORFILE_TO_LINUX_FLAG, GPIO_OUTPUT);
	GPIO_setDir(LVDATA_FROM_LINUX_BANK, LVDATA_FROM_LINUX_FLAG, GPIO_OUTPUT);
	GPIO_setDir(LVDATA_TO_LINUX_BANK, LVDATA_TO_LINUX_FLAG, GPIO_OUTPUT);


	CLR_OPTITRACKDATA_FROM_LINUX;  // Clear = tell linux DSP is ready for new Opitrack data
	CLR_DATA_FROM_LINUX;  // Clear = tell linux that DSP is ready for new data
	CLR_DATAFORFILE_TO_LINUX;  // Clear = linux not requesting data
	SET_DATA_TO_LINUX;  // Set = put float array data into shared memory for linux
	SET_IMAGE_TO_LINUX;  // Set = put image into shared memory for linux
	CLR_LVDATA_FROM_LINUX;  // Clear = tell linux that DSP is ready for new LV data
	SET_LVDATA_TO_LINUX;  // Set = put LV char data into shared memory for linux

    // clear all possible EDMA 
	EDMA3_0_Regs->SHADOW[1].ICR = 0xFFFFFFFF;
	
    // Add your init code here
}

long timecount= 0;
int whichled = 0;
// This SWI is Posted after each set of new data from the F28335
void RobotControl(void) {

	int newOPTITRACKpose = 0;
	int i = 0;

	if (0==(timecount%1000)) {
		switch(whichled) {
		case 0:
			SETREDLED;
			CLRBLUELED;
			CLRGREENLED;
			whichled = 1;
			break;
		case 1:
			CLRREDLED;
			SETBLUELED;
			CLRGREENLED;
			whichled = 2;
			break;
		case 2:
			CLRREDLED;
			CLRBLUELED;
			SETGREENLED;
			whichled = 0;
			break;
		default:
			whichled = 0;
			break;
		}
	}
	
	if (GET_OPTITRACKDATA_FROM_LINUX) {

		if (new_optitrack == 0) {
			for (i=0;i<OPTITRACKDATASIZE;i++) {
				Optitrackdata[i] = ptrshrdmem->Optitrackdata[i];
			}
			new_optitrack = 1;
		}

		CLR_OPTITRACKDATA_FROM_LINUX;

	}

	if (new_optitrack == 1) {
		OPTITRACKps = UpdateOptitrackStates(ROBOTps, &newOPTITRACKpose);
		new_optitrack = 0;
	}

	// using 400deg/s gyro
	gyro = adcA3*3.0/4096.0;
	if (settlegyro < SETTLETIME) {
		settlegyro++;
		if (settlegyro < (SETTLETIME/3)) {
			// do nothing
		} else if (settlegyro < (2*SETTLETIME/3)) {
			gyro_zero = gyro_zero + gyro/(SETTLETIME/3);
		} else {
			gyro_drift += (((gyro-gyro_zero) + old_gyro)*.0005)/(SETTLETIME/3);
			old_gyro = gyro-gyro_zero;
		}
		if(settlegyro%500 == 0) {
			LCDPrintfLine(1,"Cal Gyro -- %.1fSecs", (float)(SETTLETIME - settlegyro)/1000.0 );
			LCDPrintfLine(2,"");
			strcpy(audioClip, "b");
			playAudio = 1;
		}

		newOPTITRACKpose = 0;

		SetRobotOutputs(0,0,blueServo,orangeServo,0,0,0,0,0,0);
	} else {

		gyro_angle = gyro_angle - ((gyro-gyro_zero) + old_gyro)*.0005 + gyro_drift; 
		old_gyro = gyro-gyro_zero;
		gyro_radians = (gyro_angle * (PI/180.0)*400.0*gyro4x_gain);

		// Kalman filtering
		vel1 = (enc1 - enc1old)/(193.0*0.001);	// calculate actual velocities
		vel2 = (enc2 - enc2old)/(193.0*0.001);
		if (fabsf(vel1) > 10.0) vel1 = vel1old;	// check for encoder roll-over should never happen
		if (fabsf(vel2) > 10.0) vel2 = vel2old;
		enc1old = enc1;	// save past values
		enc2old = enc2;
		vel1old = vel1;
		vel2old = vel2;

		// Step 0: update B, u
		B[0][0] = cosf(ROBOTps.theta)*0.001;
		B[1][0] = sinf(ROBOTps.theta)*0.001;
		B[2][1] = 0.001;
		u[0][0] = 0.5*(vel1 + vel2);	// linear velocity of robot
		u[1][0] = (gyro-gyro_zero)*(PI/180.0)*400.0*gyro4x_gain;	// angular velocity in rad/s (negative for right hand angle)

		// Step 1: predict the state and estimate covariance
		Matrix3x2_Mult(B, u, Bu);					// Bu = B*u
		Matrix3x1_Add(x_pred, Bu, x_pred, 1.0, 1.0); // x_pred = x_pred(old) + Bu
		Matrix3x3_Add(P_pred, Q, P_pred, 1.0, 1.0);	// P_pred = P_pred(old) + Q
		// Step 2: if there is a new measurement, then update the state
		if (1 == newOPTITRACKpose) {
			newOPTITRACKpose = 0;
			z[0][0] = OPTITRACKps.x;	// take in the LADAR measurement
			z[1][0] = OPTITRACKps.y;
			// fix for OptiTrack problem at 180 degrees
			if (cosf(ROBOTps.theta) < -0.99) {
				z[2][0] = ROBOTps.theta;
			}
			else {
				z[2][0] = OPTITRACKps.theta;
			}
			// Step 2a: calculate the innovation/measurement residual, ytilde
			Matrix3x1_Add(z, x_pred, ytilde, 1.0, -1.0);	// ytilde = z-x_pred
			// Step 2b: calculate innovation covariance, S
			Matrix3x3_Add(P_pred, R, S, 1.0, 1.0);							// S = P_pred + R
			// Step 2c: calculate the optimal Kalman gain, K
			Matrix3x3_Invert(S, S_inv);
			Matrix3x3_Mult(P_pred,  S_inv, K);								// K = P_pred*(S^-1)
			// Step 2d: update the state estimate x_pred = x_pred(old) + K*ytilde
			Matrix3x1_Mult(K, ytilde, temp_3x1);
			Matrix3x1_Add(x_pred, temp_3x1, x_pred, 1.0, 1.0);
			// Step 2e: update the covariance estimate   P_pred = (I-K)*P_pred(old)
			Matrix3x3_Add(eye3, K, temp_3x3, 1.0, -1.0);
			Matrix3x3_Mult(temp_3x3, P_pred, P_pred);
		}	// end of correction step
	
		// set ROBOTps to the updated and corrected Kalman values.
		ROBOTps.x = x_pred[0][0];
		ROBOTps.y = x_pred[1][0];
		ROBOTps.theta = x_pred[2][0];

		if(newObs == 0 && ball_state == 0) {
			// uses xy code to step through an array of positions
			// int xy_control(float *vref_forxy, float *turn_forxy,float turn_thres, float x_pos,float y_pos,float x_desired,float y_desired,float thetaabs,float target_radius,float target_radius_near)
			if( xy_control(&vref,      		// pass vref by ref
							&turn,     		// pass turn by ref
							0.5,       		// turn saturation
							ROBOTps.x, 		//currX
							ROBOTps.y, 		//currY
							robotdest[statePos].x, // desiredX
							robotdest[statePos].y, // desiredY
							ROBOTps.theta,         // currTheta
							0.5,                  // target_radius
							0.5))                  // target_threshold
			{
				newObs = 0;
				timeCheat = timecount;
				if(robotdest[statePos].x == 0 && robotdest[statePos].y == -1) {
					strcpy(audioClip, "xfirmly grasp it");
					playAudio = 1;
				}
				statePos++;
			}
		}

		if(statePos == 11)
		{
			vref = 0;
			turn = 0;
		}
		
		if (newLADARdata == 1) {
			newLADARdata = 0;
			for (i=0;i<228;i++) {
				LADARdistance[i] = newLADARdistance[i];
				LADARangle[i] = newLADARangle[i];
				LADARdataX[i] = newLADARdataX[i];
				LADARdataY[i] = newLADARdataY[i];
			}
		}

//		unsigned char new_vision_data = 0;
//		int blue_rbar, blue_cbar, blueNumPixels;
//		int green_rbar, green_cbar, greenNumPixels;
//		int orange_rbar, orange_cbar, orangeNumPixels;

		// if flag set, get data fromshared vars and clear flag
		// only look for new balls when in course (statePos before 9)
		if(new_vision_data == 1 && statePos < 10) {

			local_blue_rbar = blue_rbar;
			local_blue_cbar = blue_cbar;
			local_blueNumPixels = blueNumPixels;

			local_green_rbar = green_rbar;
			local_green_cbar = green_cbar;
			local_greenNumPixels = greenNumPixels;

			local_orange_rbar = orange_rbar;
			local_orange_cbar = orange_cbar;
			local_orangeNumPixels = orangeNumPixels;

			switch(ball_state) {
			// check to see a ball
			case 0:
				// if we see a blue ball, turn towards it
				if(local_blueNumPixels > GOLF_BALL_THRESH) {
					ball_state = 1;
					ballColor = 1;
					initialTheta = ROBOTps.theta;
				}

				// else, if we see an orange ball, turn towards it
				else if(local_orangeNumPixels > GOLF_BALL_THRESH) {
					ball_state = 2;
					ballColor = 2;
					initialTheta = ROBOTps.theta;
				}
				else if(ballColor)
					ballColor = 0;
				break;

			// turn towards blue ball, map endLoc
			case 1:
				distance_inches = (float)(local_blue_rbar*local_blue_rbar)*distance_second + (float) local_blue_rbar*distance_first + (distance_zero);
				ballTurnError = BLUE_BALL_COL - local_blue_cbar;

				// set turn
				turn = kp_ball_turn * ballTurnError;

				if(fabsf(angularDiff(ROBOTps.theta, initialTheta) > PI))
					ball_state = 0;

				if(fabs(turn) < TURN_THRESH) {
					blueServo = 8;
					mapBall(distance_inches / 12);
					newBall = 1;
					turn = 0;
					ball_state = 3;
				}
				break;

			// turn towards orange ball, map endLoc
			case 2:
				distance_inches = (float)(local_orange_rbar*local_orange_rbar)*distance_second + (float) local_orange_rbar*distance_first + (distance_zero);
				ballTurnError = ORANGE_BALL_COL - local_orange_cbar;

				// set turn
				turn = kp_ball_turn * ballTurnError;

				if(fabsf(angularDiff(ROBOTps.theta, initialTheta) > PI))
					ball_state = 0;

				if(fabs(turn) < TURN_THRESH) {
					orangeServo = 7;
					mapBall(distance_inches / 12);
					newBall = 1;
					turn = 0;
					ball_state = 3;
				}
				break;

			// go to endLoc (and pick up ball in the process)
			case 3:
//				if(local_orangeNumPixels > GOLF_BALL_THRESH) {
//					distance_inches = (float)(local_orange_rbar*local_orange_rbar)*distance_second + (float) local_orange_rbar*distance_first + (distance_zero);
//					mapBall(distance_inches / 12);
//				}
				if( xy_control(
						&vref,      		// pass vref by ref
						&turn,     		// pass turn by ref
						0.5,       		// turn saturation
						ROBOTps.x, 		//currX
						ROBOTps.y, 		//currY
						endLocX,		 // desiredX
						endLocY,		 // desiredY
						ROBOTps.theta,         // currTheta
						0.5,                   // target_radius
						0.75)) {                 // target_threshold
					ball_state = 0;
					orangeServo = 3.0;
					blueServo = 13.0;
				}

				if (vref > 1){
					vref = 1;
				}

				if(getDist(ROBOTps.x, ROBOTps.y, robotdest[statePos].x, robotdest[statePos].y) < 0.5) {
					statePos++;
				}

				break;
			}

			new_vision_data = 0;
		}

		// add wall-following
		// find the minimum of front, right sensors
		int cnt = 0;
		float frontMin = LADARdistance[111];
		for(cnt = 98; cnt < 140; cnt++)
		{
			if (LADARdistance[cnt] < frontMin)
				frontMin = LADARdistance[cnt];
		}

		float rightMin = LADARdistance[54];
		for(cnt = 53; cnt < 65; cnt++)
		{
			if (LADARdistance[cnt] < rightMin)
				rightMin = LADARdistance[cnt];
		}

		if ((timecount%200)==0) {
			LCDPrintfLine(1, "BS:%d   | %.1f %.1f", ball_state, endLocX, endLocY);
//			LCDPrintfLine(2, "Y:%.1f  | %.1f %.1f", yVal, robotdest[statePos].x, robotdest[statePos].y);
			LCDPrintfLine(2, "X:%.1f |Y:%.1f", xVal, yVal);
		}

		// define error thresholds for each
		float frontWallError = 3000.0 - frontMin;
		float rightWallError = refright - rightMin;

		// calculate corner error
		//float corner_measurement = LADARdistance[48];
		//float corner_error = 3000.0 - corner_measurement;

		// if front wall, avoid it
		// else if right wall, avoid it
		// 		else if external corner, avoid it
		//			 else, goto location

		// if obstacle detected, follow it
		if(!ball_state) {
			if (statePos == 10)
			{
				// open servo holder, back up
				blueServo = 7.0;
				if (timecount < timeCheat + BALL_DROPOFF_TIMER)
				{
					vref = -1.5;
					turn = 0;
				}
			}
			else if (statePos == 11)
			{
				// open orange servo, back
				orangeServo = 8.0;
				if (timecount < timeCheat + BALL_DROPOFF_TIMER)
				{
					vref = -1.5;
					turn = 0;
				}
			}
			else
			{
				switch(newObs)
				{
				// No object
				case 0:
					// do xy_control above
					break;

				// Front wall avoidance
				case 1:
						if (frontWallError < FRONT_ERROR_THRESH)
						{
							findSlope(ROBOTps.x, ROBOTps.y, robotdest[statePos].x, robotdest[statePos].y);
							hitX = ROBOTps.x;
							hitY = ROBOTps.y;
							newObs = 2;
						}
					break;

				// Obstacle following part 1
				case 2:
					// Drive
					turn = -1 * kpright * rightWallError; // right wall
					vref = rightVref; // rightwall follow velocity

					// Check to see if we've left the threshold (on first discovery) before lowering the flag
					if (lineCheck(ROBOTps.x, ROBOTps.y, robotdest[statePos].x, robotdest[statePos].y) == 0)
					{
						newObs = 3;
					}

					// Check to see if we've done a half lap of the obstacle
					if (onLeftOfRobot(robotdest[statePos].x, robotdest[statePos].y) == 1)
					{
						newObs = 0;
					}

					break;
				// Obstacle following part 2
				case 3:
					// Drive
					turn = -1 * kpright * rightWallError; // right wall
					vref = rightVref; // rightwall follow velocity

					// Check to see if we've returned to the goal line
					if (lineCheck(ROBOTps.x, ROBOTps.y, robotdest[statePos].x, robotdest[statePos].y) == 1)
					{
						newObs = 0;
					}

					// Check to see if we've done a half lap of the obstacle
					if (onLeftOfRobot(robotdest[statePos].x, robotdest[statePos].y) == 1)
					{
						newObs = 0;
					}
					break;
				default:
					break;
				}

				// if front wall detected, avoid it
				if (frontWallError > FRONT_ERROR_THRESH)
				{
					turn = -1 * kpfront * frontWallError; // front wall
					vref = -0.25;
					if(newObs == 0) {
						newObs = 1;
					}
				}

				if(getDist(ROBOTps.x, ROBOTps.y, robotdest[statePos].x, robotdest[statePos].y) < 0.5) {
					statePos++;
					newObs = 0;
				}
			}
		}

		// avoid front wall while ball finding
		if (frontWallError > FRONT_ERROR_THRESH)
		{
			turn = -1 * kpfront * frontWallError; // front wall
			vref = -0.25;
		}

		if (rightWallError > 175)
		{
			turn = -1 * kpright * rightWallError; // right wall
			vref = rightVref;
		}

		if (turn > turnsat) turn = turnsat;
		if (turn < (-1*turnsat)) turn = -1*turnsat;

		SetRobotOutputs(vref,turn,blueServo,orangeServo,0,0,0,0,0,0);

		timecount++;
	}
}

pose UpdateOptitrackStates(pose localROBOTps, int * flag) {

	pose localOPTITRACKps;

	// Check for frame errors / packet loss
	if (previous_frame == Optitrackdata[OPTITRACKDATASIZE-1]) {
		frame_error++;
	}
	previous_frame = Optitrackdata[OPTITRACKDATASIZE-1];

	// Set local trackableID if first receive data
	if (firstdata){
		//trackableID = (int)Optitrackdata[OPTITRACKDATASIZE-1]; // removed to add new trackableID in shared memory
		trackableID = Optitrackdata[OPTITRACKDATASIZE-2];
		firstdata = 0;
	}

	// Check if local trackableID has changed - should never happen
	if (trackableID != Optitrackdata[OPTITRACKDATASIZE-2]) {
		trackableIDerror++;
		// do some sort of reset(?)
	}

	// Save position and yaw data
	if (isnan(Optitrackdata[0]) != 1) {  // this checks if the position data being received contains NaNs
		// check if x,y,yaw all equal 0.0 (almost certainly means the robot is untracked)
		if ((Optitrackdata[0] != 0.0) && (Optitrackdata[1] != 0.0) && (Optitrackdata[2] != 0.0)) {
			// save x,y
			// adding 2.5 so everything is shifted such that optitrack's origin is the center of the arena (while keeping all coordinates positive)
			// This was the old way for Optitrack coordinates
			//localOPTITRACKps.x = Optitrackdata[0]*FEETINONEMETER; // was 2.5 for size = 5
			//localOPTITRACKps.y = -1.0*Optitrackdata[1]*FEETINONEMETER+4.0;

			// This is the new coordinates for Motive
			localOPTITRACKps.x = -1.0*Optitrackdata[0]*FEETINONEMETER; 
			localOPTITRACKps.y = Optitrackdata[1]*FEETINONEMETER+4.0;

			// make this a function
			temp_theta = fmodf(localROBOTps.theta,(float)(2*PI));//(theta[trackableID]%(2*PI));
			tempOPTITRACK_theta = Optitrackdata[2];
			if (temp_theta > 0) {
				if (temp_theta < PI) {
					if (tempOPTITRACK_theta >= 0.0) {
						// THETA > 0, kal in QI/II, OT in QI/II
						localOPTITRACKps.theta = ((int)((localROBOTps.theta)/(2*PI)))*2.0*PI + tempOPTITRACK_theta*2*PI/360.0;
					} else {
						if (temp_theta > (PI/2)) {
							// THETA > 0, kal in QII, OT in QIII
							localOPTITRACKps.theta = ((int)((localROBOTps.theta)/(2*PI)))*2.0*PI + PI + (PI + tempOPTITRACK_theta*2*PI/360.0);
						} else {
							// THETA > 0, kal in QI, OT in QIV
							localOPTITRACKps.theta = ((int)((localROBOTps.theta)/(2*PI)))*2.0*PI + tempOPTITRACK_theta*2*PI/360.0;
						}
					}
				} else {
					if (tempOPTITRACK_theta <= 0.0) {
						// THETA > 0, kal in QIII, OT in QIII
						localOPTITRACKps.theta = ((int)((localROBOTps.theta)/(2*PI)))*2.0*PI + PI + (PI + tempOPTITRACK_theta*2*PI/360.0);
					} else {
						if (temp_theta > (3*PI/2)) {
							// THETA > 0, kal in QIV, OT in QI
							localOPTITRACKps.theta = ((int)((localROBOTps.theta)/(2*PI)))*2.0*PI + 2*PI + tempOPTITRACK_theta*2*PI/360.0;
						} else {
							// THETA > 0, kal in QIII, OT in QII
							localOPTITRACKps.theta = (floorf((localROBOTps.theta)/((float)(2.0*PI))))*2.0*PI + tempOPTITRACK_theta*2*PI/360.0;
						}
					}
				}
			} else {
				if (temp_theta > -PI) {
					if (tempOPTITRACK_theta <= 0.0) {
						// THETA < 0, kal in QIII/IV, OT in QIII/IV
						localOPTITRACKps.theta = ((int)((localROBOTps.theta)/(2*PI)))*2.0*PI + tempOPTITRACK_theta*2*PI/360.0;
					} else {
						if (temp_theta < (-PI/2)) {
							// THETA < 0, kal in QIII, OT in QII
							localOPTITRACKps.theta = ((int)((localROBOTps.theta)/(2*PI)))*2.0*PI - PI + (-PI + tempOPTITRACK_theta*2*PI/360.0);
						} else {
							// THETA < 0, kal in QIV, OT in QI
							localOPTITRACKps.theta = ((int)((localROBOTps.theta)/(2*PI)))*2.0*PI + tempOPTITRACK_theta*2*PI/360.0;
						}
					}
				} else {
					if (tempOPTITRACK_theta >= 0.0) {
						// THETA < 0, kal in QI/II, OT in QI/II
						localOPTITRACKps.theta = ((int)((localROBOTps.theta)/(2*PI)))*2.0*PI - PI + (-PI + tempOPTITRACK_theta*2*PI/360.0);
					} else {
						if (temp_theta < (-3*PI/2)) {
							// THETA < 0, kal in QI, OT in QIV
							localOPTITRACKps.theta = ((int)((localROBOTps.theta)/(2*PI)))*2.0*PI - 2*PI + tempOPTITRACK_theta*2*PI/360.0;
						} else {
							// THETA < 0, kal in QII, OT in QIII
							localOPTITRACKps.theta = ((int)((localROBOTps.theta)/(2*PI)))*2.0*PI + tempOPTITRACK_theta*2*PI/360.0;
						}
					}
				}
			}
			*flag = 1;
		}
	}
	return localOPTITRACKps;
}

