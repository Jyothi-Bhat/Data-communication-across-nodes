#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <hw_nvic.h>
#include <hw_types.h>
#include <math.h>
#include "tm4c123gh6pm.h"

#define RED_LED      (*((volatile uint32_t *)(0x42000000 + (0x400253FC-0x40000000)*32 + 1*4)))
#define GREEN_LED    (*((volatile uint32_t *)(0x42000000 + (0x400253FC-0x40000000)*32 + 3*4)))
#define BLUE_LED      (*((volatile uint32_t *)(0x42000000 + (0x400253FC-0x40000000)*32 + 2*4)))

#define PUSH_BUTTON  (*((volatile uint32_t *)(0x42000000 + (0x400253FC-0x40000000)*32 + 4*4)))

#define externRED_LED      (*((volatile uint32_t *)(0x42000000 + (0x400043FC-0x40000000)*32 + 7*4)))
#define externGREEN_LED    (*((volatile uint32_t *)(0x42000000 + (0x400063FC-0x40000000)*32 + 7*4)))

#define receivePin  (*((volatile uint32_t *)(0x42000000 + (0x400063FC-0x40000000)*32 + 4*4)))
#define dataPin  (*((volatile uint32_t *)(0x42000000 + (0x400063FC-0x40000000)*32 + 5*4)))
#define DEenable  (*((volatile uint32_t *)(0x42000000 + (0x400063FC-0x40000000)*32 + 6*4)))

#define MAX_CHARS 50                           //static array size
#define MAX_BUFSIZE 5                         //buffer size
#define T 500                                     //500ms // 50-70ms
#define T0 100                                  //100ms should be 10ms

bool valid_cmd, cs_enable, ran_enable, ack_enable, new_entry;                    //global flag variables for command validity
bool valid[MAX_BUFSIZE];                                                //global flag variable for stack availability

//defining global stack variables
uint8_t size[MAX_BUFSIZE], destAdd[MAX_BUFSIZE], seqID[MAX_BUFSIZE], chan[MAX_BUFSIZE], data[MAX_BUFSIZE], retrans[MAX_BUFSIZE];
uint8_t checksum[MAX_BUFSIZE], cmdNum[MAX_BUFSIZE], ran[MAX_BUFSIZE], ack[MAX_BUFSIZE], retrans[MAX_BUFSIZE];
uint8_t rgb_data[MAX_BUFSIZE][3];
uint8_t currentID = 255, ack_check_index, sourceAdd = 25, ack_index;
uint32_t timeout;
bool in_progress, onlymine;

uint16_t red, blue, green;
uint8_t minArgs, cn, dataSize, phase_tx = 0, index;
char original_string[MAX_CHARS];
uint8_t position[MAX_CHARS];
char message[10][MAX_CHARS];
char DA[MAX_CHARS], CH[MAX_CHARS];

uint8_t verify_checksum = 0;
uint8_t phase_rx = 0, rx_ack;
uint8_t rx_dest, rx_source, rx_seqID, rx_cmd, rx_channel, rx_size, rx_data, rx_checksum, rx_rgb_data[3];

// Blocking function that returns only when SW1 is pressed;
void waitPbPress()
{
    while(PUSH_BUTTON);
}

//initialize hardware
void init_hw()
{
    // Configure HW to work with 16 MHz XTAL, PLL enabled, system clock of 40 MHz
    SYSCTL_RCC_R = SYSCTL_RCC_XTAL_16MHZ | SYSCTL_RCC_OSCSRC_MAIN | SYSCTL_RCC_USESYSDIV | (4 << SYSCTL_RCC_SYSDIV_S) | SYSCTL_RCC_USEPWMDIV | SYSCTL_RCC_PWMDIV_2;

    // Set GPIO ports to use APB (not needed since default configuration -- for clarity)
    SYSCTL_GPIOHBCTL_R = 0;

    // Enable GPIO port A, C and F peripherals
    SYSCTL_RCGC2_R = SYSCTL_RCGC2_GPIOA | SYSCTL_RCGC2_GPIOC | SYSCTL_RCGC2_GPIOF | SYSCTL_RCGC2_GPIOE;

    // Configure LED and pushbutton pins
    GPIO_PORTF_DIR_R = 0x0E;  // bits 1 and 3 are outputs, other pins are inputs
    GPIO_PORTF_DR2R_R = 0x0E; // set drive strength to 2mA (not needed since default configuration -- for clarity)
    GPIO_PORTF_DEN_R = 0x1E;  // enable LEDs and pushbuttons
    GPIO_PORTF_PUR_R = 0x10;  // enable internal pull-up for push button
    GPIO_PORTA_DIR_R = 0xC0;  // bits 1 and 3 are outputs, other pins are inputs
    GPIO_PORTA_DR2R_R = 0xC0; // set drive strength to 2mA (not needed since default configuration -- for clarity)
    GPIO_PORTA_DEN_R = 0xC0;  // enable LEDs and pushbuttons

    GPIO_PORTC_DIR_R |= 0x80;  // bits 1 and 3 are outputs, other pins are inputs
    GPIO_PORTC_DR2R_R |= 0x80; // set drive strength to 2mA (not needed since default configuration -- for clarity)
    GPIO_PORTC_DEN_R |= 0x80;

    // Configure UART0 pins
    SYSCTL_RCGCUART_R |= SYSCTL_RCGCUART_R0;         // turn-on UART0, leave other uarts in same status
    GPIO_PORTA_DEN_R |= 3;                           // default, added for clarity
    GPIO_PORTA_AFSEL_R |= 3;                         // default, added for clarity
    GPIO_PORTA_PCTL_R = GPIO_PCTL_PA1_U0TX | GPIO_PCTL_PA0_U0RX;

    // Configure UART0 to 115200 baud, 8N1 format (must be 3 clocks from clock enable and config writes)
    UART0_CTL_R = 0;                                 // turn-off UART0 to allow safe programming
    UART0_CC_R = UART_CC_CS_SYSCLK;                  // use system clock (40 MHz)
    UART0_IBRD_R = 21;                               // r = 40 MHz / (Nx115.2kHz), set floor(r)=21, where N=16
    UART0_FBRD_R = 45;                               // round(fract(r)*64)=45
    UART0_LCRH_R = UART_LCRH_WLEN_8 | UART_LCRH_FEN; // configure for 8N1 w/ 16-level FIFO
    UART0_CTL_R = UART_CTL_TXE | UART_CTL_RXE | UART_CTL_UARTEN ; // enable TX, RX, and module

    // Configure UART1 pins
    SYSCTL_RCGCUART_R |= SYSCTL_RCGCUART_R1;         // turn-on UART1, leave other uarts in same status
    GPIO_PORTC_DIR_R = 0X40;
    GPIO_PORTC_DR2R_R = 0X40;
    GPIO_PORTC_DEN_R = 0X70;                         // default, added for clarity
    GPIO_PORTC_AFSEL_R |= 0x30;                         // default, added for clarity
    GPIO_PORTC_PCTL_R |= GPIO_PCTL_PC5_U1TX | GPIO_PCTL_PC4_U1RX;

    // Configure UART1 to 38400 baud, 8N1 format (must be 3 clocks from clock enable and config writes)
    UART1_CTL_R = 0;                                 // turn-off UART1 to allow safe programming
    UART1_CC_R = UART_CC_CS_SYSCLK;                  // use system clock (40 MHz)
    UART1_IBRD_R = 65;                               // r = 40 MHz / (Nx38400Hz), set floor(r)=65, where N=16
    UART1_FBRD_R = 07;                               // round(fract(r)*64)=7
    UART1_LCRH_R = UART_LCRH_SPS | UART_LCRH_PEN | UART_LCRH_WLEN_8 | UART_LCRH_FEN | UART_LCRH_EPS; // configure for 8N1 w/ 16-level FIFO
    UART1_CTL_R = UART_CTL_TXE | UART_CTL_RXE | UART_CTL_UARTEN; // enable TX, RX, and module

    // Configure Timer 1 as the time base
        SYSCTL_RCGCTIMER_R |= SYSCTL_RCGCTIMER_R1;       // turn-on timer
        TIMER1_CTL_R &= ~TIMER_CTL_TAEN;                 // turn-off timer before reconfiguring
        TIMER1_CFG_R = TIMER_CFG_32_BIT_TIMER;           // configure as 32-bit timer (A+B)
        TIMER1_TAMR_R = TIMER_TAMR_TAMR_PERIOD;          // configure for periodic mode (count down)
        TIMER1_TAILR_R = 0x9C40;                      // set load value to 40e9 for 1 mHz interrupt rate
        //TIMER1_TAILR_R = 0x2625A00;
        TIMER1_IMR_R = TIMER_IMR_TATOIM;                 // turn-on interrupts
        NVIC_EN0_R |= 1 << (INT_TIMER1A-16);             // turn-on interrupt 37 (TIMER1A)
        TIMER1_CTL_R |= TIMER_CTL_TAEN;                  // turn-on timer

        //PWM configuration
            SYSCTL_RCGCPWM_R |= SYSCTL_RCGCPWM_R1;             // turn-on PWM0 module
            __asm(" NOP");                                   // wait 3 clocks
            __asm(" NOP");
            __asm(" NOP");
            SYSCTL_SRPWM_R = SYSCTL_SRPWM_R1;                // reset PWM1 module
            SYSCTL_SRPWM_R = 0;                              // leave reset state
            PWM1_2_CTL_R = 0;                                // turn-off PWM0 generator 1
            PWM1_3_CTL_R = 0;                                // turn-off PWM0 generator 2
            PWM1_2_GENB_R = PWM_1_GENB_ACTCMPBD_ZERO | PWM_1_GENB_ACTLOAD_ONE;  // output 3 on PWM0, gen 1b, cmpb
            PWM1_3_GENA_R = PWM_1_GENA_ACTCMPAD_ZERO | PWM_1_GENA_ACTLOAD_ONE;  // output 4 on PWM0, gen 2a, cmpa
            PWM1_3_GENB_R = PWM_1_GENB_ACTCMPBD_ZERO | PWM_1_GENB_ACTLOAD_ONE;
                      // output 5 on PWM0, gen 2b, cmpb
            PWM1_2_LOAD_R = 1024;                            // set period to 40 MHz sys clock / 2 / 1024 = 19.53125 kHz
            PWM1_3_LOAD_R = 1024;
            PWM1_INVERT_R = PWM_INVERT_PWM5INV | PWM_INVERT_PWM6INV | PWM_INVERT_PWM7INV;
                                                             // invert outputs for duty cycle increases with increasing compare values
            PWM1_2_CMPB_R = 0;                               // red off (0=always low, 1023=always high)
            PWM1_3_CMPB_R = 0;                               // green off
            PWM1_3_CMPA_R = 0;                               // blue off

            PWM1_2_CTL_R = PWM_1_CTL_ENABLE;                 // turn-on PWM0 generator 1
            PWM1_3_CTL_R = PWM_1_CTL_ENABLE;                 // turn-on PWM0 generator 2
            PWM1_ENABLE_R = PWM_ENABLE_PWM5EN | PWM_ENABLE_PWM6EN | PWM_ENABLE_PWM7EN;
                                                             // enable outputs

}

setRgbColor()
{
    GPIO_PORTF_AFSEL_R |= 0x0E; // select auxilary function for bit 5
    GPIO_PORTF_PCTL_R |= GPIO_PCTL_PF1_M1PWM5 | GPIO_PCTL_PF2_M1PWM6 | GPIO_PCTL_PF3_M1PWM7; // enable PWM on bits 4 and 5

    PWM1_2_CMPB_R = rx_rgb_data[0];
    PWM1_3_CMPA_R = rx_rgb_data[1];
    PWM1_3_CMPB_R = rx_rgb_data[2];

    timeout = 16384;
    while(timeout)
        timeout--;

    timeout = 16384;
    while(timeout)
        timeout--;

    GPIO_PORTF_AFSEL_R &= ~0x0E; // select auxilary function for bit 5
    GPIO_PORTF_PCTL_R &= ~GPIO_PCTL_PF1_M1PWM5;
    GPIO_PORTF_PCTL_R &= ~ GPIO_PCTL_PF2_M1PWM6;
    GPIO_PORTF_PCTL_R &= ~GPIO_PCTL_PF3_M1PWM7; // enable PWM on bits 4 and 5
}


// Approximate busy waiting (in units of microseconds), given a 40 MHz system clock
void waitMicrosecond(uint32_t us)
{
    __asm("WMS_LOOP0:   MOV  R1, #6");          // 1
    __asm("WMS_LOOP1:   SUB  R1, #1");          // 6
    __asm("             CBZ  R1, WMS_DONE1");   // 5+1*3
    __asm("             NOP");                  // 5
    __asm("             NOP");                  // 5
    __asm("             B    WMS_LOOP1");       // 5*2 (speculative, so P=1)
    __asm("WMS_DONE1:   SUB  R0, #1");          // 1
    __asm("             CBZ  R0, WMS_DONE0");   // 1
    __asm("             NOP");                  // 1
    __asm("             B    WMS_LOOP0");       // 1*2 (speculative, so P=1)
    __asm("WMS_DONE0: BX LR");                        // ---
                                                // 40 clocks/us + error
    return;
}

//to convert the function to lower case
void toLowerCase()
{
   uint8_t i = 0;
   while(original_string[i]!='\0')
   {
       if((original_string[i] >= 65) && (original_string[i] <= 90))
       {
            original_string[i] += 32;
       }
       i++;
   }
   return;
}

//Blocking function to generate random number
uint16_t generate_ran_number()
{
    uint16_t seed = 255;
    seed = retrans[ack_index] * seed * rand();
    timeout = 2048;
    while(timeout)
        timeout--;
    return seed;

}

// Blocking function that writes a serial character when the UART buffer is not full
void putcUart0(char c)
{
    while (UART0_FR_R & UART_FR_TXFF);
    UART0_DR_R = c;
    return;
}

// Blocking function that writes a serial number when the UART buffer is not full
void putnUart0(uint8_t n)
{
    while (UART0_FR_R & UART_FR_TXFF);
    int8_t i,x;
    int8_t count = -1;
    char c, temp[100];
    if(n==0)
        putcUart0(48);
    while(n!=0)
    {
        x = n%10;
        x += 48;
        c = x;
        temp[++count] = c;
        n /= 10;
    }
    for(i=count;i>=0;i--)
        putcUart0(temp[i]);
    return;
}

// Blocking function that writes a string when the UART buffer is not full
void putsUart0(char* str)
{
    uint8_t i;
    for (i = 0; str[i]!='\0'; i++)
        putcUart0(str[i]);
    return;
}


// Blocking function that returns character with serial data once the buffer is not empty
char getcUart0()
{
    while (UART0_FR_R & UART_FR_RXFE);
    return UART0_DR_R & 0xFF;
}

// Blocking function that returns string with serial data once the buffer is not empty
void getsUart0(char *o_string)
{
    uint32_t count = 0;
    char c;

getchar :   c = getcUart0();
            if(c==13)               //carriage return
            {
done :          o_string[count++] = 0;
                return;
            }
            if(c==8)            //backspace
            {
                if(count>0)
                    count--;
                goto getchar;
            }
            if((c==32) || (48<=c<=57) || (65<=c<=90) || (97<=c<=122))
            {
                o_string[count] = c;
                count++;
                if(count>= MAX_CHARS)
                    goto done;
                else goto getchar;
            }
            else
                goto getchar;
}

//blocking function to copy a string from array
void strcp(char *s1, char *s2)
{
    int i=0;
    while(s2[i]!='\0')
    {
        s1[i]=s2[i];
        i++;
    }
    s1[i]='\0';
    return;
}

//Blocking function calculating fields and position vector
void transform_string()
{
    uint8_t slength = strlen(original_string);
    uint8_t i=0,j=0;
    for(j=0;j<MAX_CHARS;j++)
        position[j] = 0;
    minArgs = 0;
    j=0;

    while(i<slength)
        {
            if(i==0)
            {
                if(original_string[i]==32)
                    i = i+1;
                else
                {
                    position[j]=0;
                    j++;
                    i++;
                    (minArgs)=(minArgs)+1;
                }
                continue;
            }
            if(original_string[i]==32)
            {
                original_string[i]='\0';
                i++;
                while(original_string[i]==32)
                {
                    original_string[i]='\0';
                    i = i+1;
                }
                 position[j]=i;
                 j = j+1;
                 minArgs = minArgs + 1;
             }
            i = i+1;
        }
  /*  putsUart0("\r\n");
    for(j=0;j<minArgs;j++)
        putsUart0(original_string+position[j]);
    putsUart0("\r\n");  */
        return;
}

//blocking function extracting parameters from the copies string
void getCommand()
{
    uint8_t i;
    //j;
  /*  for(i=0;i<10;i++)
    {
        for(j=0;j<MAX_CHARS;j++)
            message[i][j] = '\0';
    }       */
    putsUart0("\r\n");
    for(i=0;i<minArgs;i++)
    {
        strcp(message[i],(original_string+position[i]));
        putsUart0(message[i]);
    }
    putsUart0("\r\n");

    return;
}

//blocking function confirming the correct commands
void isCommand()
{
    valid_cmd = false;
    onlymine = false;

    if(strcmp(message[0],"reset")==0)
    {
        if(minArgs == 2)
        {
            strcp(DA,message[1]);
            strcp(message[2],"\0");
            strcp(message[3],"\0");
            dataSize = 0;
            cn = 0x7F;
            strcp(CH,'\0');
            valid_cmd = true;
        }
        else
        valid_cmd = false;
    }
    else if(strcmp(message[0],"cs")==0)
    {
        if(minArgs==2)
        {
            if(strcmp(message[1],"on")==0 || strcmp(message[1],"off")==0)
            {
                strcp(message[3],message[1]);
                strcp(message[1],"\0");
                strcp(message[2],"\0");
                dataSize = 1;
                onlymine = true;
                valid_cmd = true;
                strcp(DA,'\0');
                strcp(CH,'\0');
                if(strcmp(message[3],"on")==0)
                    cs_enable = true;
                else
                    cs_enable = false;
            }
            else
            valid_cmd = false;
        }
        else
        valid_cmd = false;
    }
    else if(strcmp(message[0],"random")==0)
    {
        if(minArgs == 2)
        {
            if(strcmp(message[1],"on")==0 || strcmp(message[1],"off")==0)
            {
                strcp(message[3],message[1]);
                strcp(message[1],"\0");
                strcp(message[2],"\0");
                dataSize = 1;
                onlymine = true;
                valid_cmd = true;
                strcp(DA,'\0');
                strcp(CH,'\0');
                if(strcmp(message[1],"on")==0)
                    ran_enable = true;
                else
                    ran_enable = false;
            }
            else
            valid_cmd = false;
        }
        else
        valid_cmd = false;
    }
    else if(strcmp(message[0],"set")==0)
    {
        if(minArgs == 4)
        {
            strcp(DA,message[1]);
            strcp(CH,message[2]);
            dataSize = 1;
            valid_cmd = true;
        }
        else
        valid_cmd = false;
    }
    else if(strcmp(message[0],"get")==0)
    {
        if(minArgs == 3)
        {
            strcp(DA,message[1]);
            strcp(CH,message[2]);
            strcp(message[3],"\0");
            dataSize = 0;
            cn = 0x20;
            valid_cmd = true;
        }
        else
        valid_cmd = false;
    }
    else if(strcmp(message[0],"poll")==0)
    {
        if(minArgs == 1)
        {
            strcp(message[1],"\0");
            strcp(message[2],"\0");
            strcp(message[3],"\0");
            dataSize = 0;
            cn = 0x78;
            valid_cmd = true;
            strcp(DA,'\0');
            strcp(CH,'\0');
        }
        else
        valid_cmd = false;
    }
    else if(strcmp(message[0],"sa")==0)
    {
        if(minArgs == 3)
        {
            strcp(message[3],message[2]);
            strcp(message[2],"\0");
            strcp(DA,message[1]);
            dataSize = 0;
            cn = 0x7A;
            valid_cmd = true;
        }
        else
        valid_cmd = false;
    }
    else if(strcmp(message[0],"ack")==0)
    {
        if(minArgs == 2)
        {
            if(strcmp(message[1],"on")==0 || strcmp(message[1],"off")==0)
            {
               strcp(message[3],message[1]);
               strcp(message[1],"\0");
               strcp(message[2],"\0");
               dataSize = 1;
               valid_cmd = true;
               strcp(DA,'\0');
               onlymine = true;
               if(strcmp(message[3],"on")==0)
                   ack_enable = true;
               else
                   ack_enable = false;
            }
            else
            valid_cmd = false;
        }
        else
        valid_cmd = false;
    }
    else if(strcmp(message[0],"rgb")==0)
    {
        if(minArgs == 6)
        {
            strcp(DA,message[1]);
            strcp(CH,message[2]);
            dataSize = 3;
            cn = 0x48;
            valid_cmd = true;
        }
        else
            valid_cmd = false;
        }
    else
        valid_cmd = false;
    return;
}

//blocking function for storing stack entry
void store_buffer()
{
    uint8_t i=0;

    while(i<MAX_BUFSIZE)
    {
        if(!valid[i])
        {
            currentID--;

            if(ack_enable)
                ack[i] = 1;
            else
                ack[i] = 0;

            if(ran_enable)
                ran[i] = 1;
            else
                ran[i] = 0;


           if(strcmp(DA,'\0')!=0)
               destAdd[i] = atoi(DA);
           else if(cn == 0x78)
               destAdd[i] = 255;
           else
               destAdd[i] = 0;

            seqID[i] = currentID;
            cmdNum[i] = cn;

            if(strcmp(CH,'\0')!=0)
                chan[i] = atoi(CH);
            else
                chan[i] = 0;

            size[i] = dataSize;

            if(dataSize == 3)
            {
                rgb_data[i][0] = atoi(message[3]);
                rgb_data[i][1] = atoi(message[4]);
                rgb_data[i][2] = atoi(message[5]);
            }
            else if(dataSize == 1)
            {
                if(strcmp(message[3],'\0')!=0)
                    data[i] = atoi(message[3]);
                else
                    data[i] = 0;
            }
            else
                data[i] = 0;

            valid[i]=true;
            new_entry = false;

            if(destAdd[i] != 0)
            {
                putsUart0("\r\n");
                putsUart0("                   QUEUING MESSAGE ");
                putnUart0(seqID[i]);
                putsUart0("\r\n");
            }

       break;
        }

        i++;
        if(i==MAX_BUFSIZE)
            putsUart0("sorry the buffer is full :( \r\n");
    }

    return;
}

//bloacking function to transmit package
uint8_t send_Message()
{
    do
    {
        switch(phase_tx)
        {
            case 0:
                if((UART1_FR_R & UART_FR_TXFF) || (UART1_FR_R & UART_FR_BUSY))
                    return 0;
                UART1_LCRH_R &= ~UART_LCRH_EPS;                                               //enable 9th bit
                UART1_DR_R = destAdd[index];
                phase_tx++;
            break;

            case 1:
                if((UART1_FR_R & UART_FR_TXFF) || (UART1_FR_R & UART_FR_BUSY))
                    return 0;
                UART1_LCRH_R |= UART_LCRH_EPS;                                              //disable 9th bit
                UART1_DR_R = sourceAdd;
                phase_tx++;
            break;

            case 2:
                if(UART1_FR_R & UART_FR_TXFF)
                    return 0;
                UART1_DR_R = seqID[index];
                phase_tx++;
            break;

            case 3:
                if(UART1_FR_R & UART_FR_TXFF)
                    return 0;
                if(ack[index])
                    cmdNum[index] |= 0x80;
                UART1_DR_R = cmdNum[index];
                phase_tx++;
            break;

            case 4:
                if(UART1_FR_R & UART_FR_TXFF)
                    return 0;
                UART1_DR_R = chan[index];
                phase_tx++;
            break;

            case 5:
                if(UART1_FR_R & UART_FR_TXFF)
                    return 0;
                UART1_DR_R = size[index];
                phase_tx++;
            break;

            case 6:
                if(size[index] > 0)
                {
                    if(UART1_FR_R & UART_FR_TXFF)
                        return 0;
                    if(size[index] == 3)
                    {
                        UART1_DR_R = rgb_data[index][0];
                        while(UART1_FR_R & UART_FR_TXFF);
                        UART1_DR_R = rgb_data[index][1];
                        while(UART1_FR_R & UART_FR_TXFF);
                        UART1_DR_R = rgb_data[index][2];
                        checksum[index] = rgb_data[index][0] + rgb_data[index][1] + rgb_data[index][2] + size[index] + chan[index] + cmdNum[index] + seqID[index] + sourceAdd + destAdd[index];
                    }
                    else
                    {
                        UART1_DR_R = data[index];
                        checksum[index] = data[index]+ size[index] + chan[index] + cmdNum[index] + seqID[index] + sourceAdd + destAdd[index];
                    }
                    while(UART1_FR_R & UART_FR_TXFF);
                    checksum[index] = ~checksum[index];
                    UART1_DR_R = checksum[index];
                }

                if(size[index]==0)
                {
                    while(UART1_FR_R & UART_FR_TXFF);
                    checksum[index] = chan[index] + cmdNum[index] + seqID[index] + sourceAdd + destAdd[index];
                    checksum[index] = ~checksum[index];
                    UART1_DR_R = checksum[index];
                }

                externRED_LED = 1;
                timeout = 16384;
                while(timeout)
                    timeout--;
                externRED_LED = 0;

                phase_tx = 0;
                break;
            default:
                break;
        }

    }

    while(phase_tx != 0);

    putsUart0("\r\n");
    putsUart0("    TRANSMITTING MESSAGE  ");
    putnUart0(seqID[index]);
    putsUart0("  , ATTEMPT ");
    putnUart0(retrans[index]+1);
    putsUart0("\r\n");
    putsUart0("\r\n");
    putsUart0("sent message:  ");
    putnUart0(destAdd[index]);
    putsUart0("  ");
    putnUart0(sourceAdd);
    putsUart0("  ");
    putnUart0(seqID[index]);
    putsUart0("  ");
    putnUart0(cmdNum[index]);
    putsUart0("  ");
    putnUart0(chan[index]);
    putsUart0("  ");
    putnUart0(size[index]);

    if(size[index] == 3)
    {
        putsUart0("  ");
        putnUart0(rgb_data[index][0]);
        putsUart0("  ");
        putnUart0(rgb_data[index][1]);
        putsUart0("  ");
        putnUart0(rgb_data[index][2]);
    }
    else if(size[index] == 1)
    {
        putsUart0("  ");
        putnUart0(data[index]);
    }
    else
        ;

    putsUart0("  ");

    putnUart0(checksum[index]);
    putsUart0("  ");
    putsUart0("Re-try number = ");
    putnUart0(retrans[index]);
    putsUart0("\r\n");
        return 1;
}

uint8_t receive_Message()
{
    uint8_t j, r_data, rx_check, rx_ack_cmd;
    uint16_t rx_12data;

    do
    {
        switch(phase_rx)
        {
            case 0:
                if(UART1_FR_R & UART_FR_RXFE)
                    return 0;
                UART1_LCRH_R &= ~UART_LCRH_EPS;
                rx_12data = UART1_DR_R;
                rx_check = rx_12data & 0x200;
                r_data = rx_12data &0xFF;
                if(rx_check != 0)
                    return 2;
                rx_dest = r_data;
                if(rx_dest != sourceAdd)
                    if(rx_dest != 255)
                        return 2;
                phase_rx++;
            break;

            case 1:
                if(UART1_FR_R & UART_FR_RXFE)
                    return 0;
                UART1_LCRH_R |= UART_LCRH_EPS;
                rx_12data = UART1_DR_R;
                rx_check = rx_12data & 0x200;
                r_data = rx_12data &0xFF;
                if(rx_check != 0)
                    return 2;
                rx_source = r_data;
                if(rx_source == sourceAdd)
                    return 2;
                phase_rx++;
            break;

            case 2:
                if(UART1_FR_R & UART_FR_RXFE)
                    return 0;
                rx_12data = UART1_DR_R;
                rx_check = rx_12data & 0x200;
                r_data = rx_12data &0xFF;
                if(rx_check != 0)
                    return 2;
                rx_seqID = r_data;
                phase_rx++;
            break;

            case 3:
                if(UART1_FR_R & UART_FR_RXFE)
                    return 0;
                rx_12data = UART1_DR_R;
                rx_check = rx_12data & 0x200;
                r_data = rx_12data &0xFF;
                if(rx_check != 0)
                    return 2;
                rx_cmd = r_data;
                rx_ack_cmd = rx_cmd;
                if(r_data&0x80)
                {
                    rx_ack = 1;
                    rx_ack_cmd &= 0x7F;
                }
                phase_rx++;
           break;

           case 4:
               if(UART1_FR_R & UART_FR_RXFE)
                   return 0;
               rx_12data = UART1_DR_R;
               rx_check = rx_12data & 0x200;
               r_data = rx_12data &0xFF;
               if(rx_check != 0)
                   return 2;
               rx_channel = r_data;
               phase_rx++;
          break;

          case 5:
              if(UART1_FR_R & UART_FR_RXFE)
                  return 0;
              rx_12data = UART1_DR_R;
              rx_check = rx_12data & 0x200;
              r_data = rx_12data &0xFF;
              if(rx_check != 0)
                  return 2;
              rx_size = r_data;
              phase_rx++;
         break;

          case 6:
              if(rx_size > 0)
              {
                  if(UART1_FR_R & UART_FR_RXFE)
                      return 0;
                  if(rx_size == 3)
                  {
                      for(j=0;j<3;j++)
                      {
                          rx_12data = UART1_DR_R;
                          rx_check = rx_12data & 0x200;
                          r_data = rx_12data &0xFF;
                          if(rx_check != 0)
                              return 2;
                          rx_rgb_data[j] = r_data;
                          while(UART1_FR_R & UART_FR_RXFE);
                      }
                     verify_checksum = sourceAdd + rx_source + rx_cmd + rx_channel + rx_rgb_data[0] + rx_rgb_data[1] + rx_rgb_data[2] + rx_size + rx_seqID;
                  }
                  else
                  {
                      rx_12data = UART1_DR_R;
                      rx_check = rx_12data & 0x200;
                      r_data = rx_12data &0xFF;
                      if(rx_check != 0)
                          return 2;
                      rx_data = r_data;
                      verify_checksum = sourceAdd + rx_source + rx_cmd + rx_channel + rx_data + rx_size + rx_seqID;
                  }

                  while(UART1_FR_R & UART_FR_RXFE);
                  rx_12data = UART1_DR_R;
                  rx_check = rx_12data & 0x200;
                  r_data = rx_12data &0xFF;
                  if(rx_check != 0)
                      return 2;
                  rx_checksum = r_data;
              }

         if(rx_size == 0)
         {
             while(UART1_FR_R & UART_FR_RXFE);
             rx_12data = UART1_DR_R;
             rx_check = rx_12data & 0x200;
             r_data = rx_12data &0xFF;
             if(rx_check != 0)
                 return 2;
             rx_checksum = r_data;
             verify_checksum = sourceAdd + rx_source + rx_cmd + rx_channel + rx_size + rx_seqID;
         }

          verify_checksum = ~verify_checksum;
          externGREEN_LED = 1;
          timeout = 16384;
          while(timeout)
              timeout--;
          externGREEN_LED = 0;

          phase_rx = 0;
          break;
          default:
              break;
    }
  }
    while(phase_rx!=0);

    putsUart0("\r\n");
    putsUart0("received message:  ");
    putnUart0(rx_dest);
    putsUart0("  ");
    putnUart0(rx_source);
    putsUart0("  ");
    putnUart0(rx_seqID);
    putsUart0("  ");
    putnUart0(rx_cmd);
    putsUart0("  ");
    putnUart0(rx_channel);
    putsUart0("  ");
    putnUart0(rx_size);
    putsUart0("  ");
    if(rx_size == 0)
        goto end;
    else if(rx_size == 3)
    {
        putnUart0(rx_rgb_data[0]);
        putsUart0("  ");
        putnUart0(rx_rgb_data[1]);
        putsUart0("  ");
        putnUart0(rx_rgb_data[2]);
        putsUart0("  ");
    }
    else
    {
        putnUart0(rx_data);
        putsUart0("  ");
    }
end:
    putnUart0(rx_checksum);
    putsUart0("\r\n");

    if(rx_ack)
        rx_cmd = rx_ack_cmd;

    return 1;
}

void send_cmd_data(uint8_t cdata)
{
    uint8_t i = 0;
    uint8_t tx_m;
    while(i<MAX_BUFSIZE)
    {
        if(!valid[i])
        {
            destAdd[i] = rx_source;
            seqID[i] = currentID--;

            if(rx_cmd == 0x20)
                cmdNum[i] = 0x21;
            else
                cmdNum[i] = 0x79;

            chan[i] = 0;
            size[i] = 1;
            data[i] = cdata;

            UART1_CTL_R |= UART_CTL_TXE;
            UART1_CTL_R &= ~UART_CTL_RXE;
            DEenable = 1;

            index = i;
tryagain:
            tx_m = send_Message();

            if(!tx_m)
            {
                timeout = 16384;
                while(timeout)
                    timeout--;
                goto tryagain;
            }

            else
            {
                while(UART1_FR_R & UART_FR_BUSY);
                DEenable = 0;
                break;
            }
       }

       i++;
       if(i==MAX_BUFSIZE)
           putsUart0("sorry, the buffer is full, can't respond to the message received :( \r\n");
        }
        return;

}

void perform_task()
{
    uint8_t cmd_data;

    if(verify_checksum == rx_checksum)
    {
        if(rx_cmd == 0 && rx_channel == 21 && rx_data == 1)
            GREEN_LED = 1;

        else if(rx_cmd == 0 && rx_channel == 21 && rx_data == 0)
            GREEN_LED = 0;

        else if(rx_cmd == 0 && rx_channel == 22 && rx_data == 1)
            RED_LED = 1;

        else if(rx_cmd == 0 && rx_channel == 22 && rx_data == 0)
            RED_LED = 0;

        else if(rx_cmd == 0x20)
        {
            if(rx_channel == 21)
            {
                if(GREEN_LED)
                    cmd_data = 1;
                else
                    cmd_data = 0;
            }
            if(rx_channel == 22)
            {
                if(RED_LED)
                    cmd_data = 1;
                else
                    cmd_data = 0;
            }
            if(rx_channel == 23)
            {
                if(PUSH_BUTTON)
                    cmd_data = 1;
                else
                    cmd_data = 0;
            }

            send_cmd_data(cmd_data);
        }

        else if(rx_cmd == 0x78)
        {
            cmd_data = sourceAdd;
            send_cmd_data(cmd_data);
        }

        else if(rx_cmd == 0x48)
            setRgbColor();

        else if(rx_cmd == 0x79)
           putsUart0("poll response received \r\n");

        else if(rx_cmd == 0x7A)
            sourceAdd = rx_data;

        else if(rx_cmd == 0x7F)
        {
            putsUart0("\r\n");
            putsUart0("resetting this device \r\n");
            HWREG(NVIC_APINT) = NVIC_APINT_VECTKEY | NVIC_APINT_SYSRESETREQ;
        }

        else
            ;
    }

    else
    {
           externGREEN_LED = 1;
           putsUart0("BAD CHECKSUM \r\n");
    }
    return;

}

void tx_ack_handle()
{
    uint16_t delay, ran_num;
    uint8_t tx_m, rx_m;

again:

    if(!ran[ack_index])
        delay = T0 * pow(2,retrans[ack_index]);
    else
    {
        ran_num = generate_ran_number();
        delay = T * pow(2,retrans[ack_index]) * ran_num;
    }

    UART1_CTL_R |= UART_CTL_RXE;
    UART1_CTL_R &= ~UART_CTL_TXE;

    while(delay)
    {
        delay--;
        timeout = 2048;
        while(timeout)
            timeout--;
    }

    rx_m = receive_Message();

    if(rx_m==1)
        goto check;
    else if(rx_m == 0)
        goto check;
    else
        phase_rx = 0;

check:

    if(rx_cmd == 0x70 && rx_data == seqID[ack_index])
        ack[ack_index] = 0;

    if(!ack[ack_index])
    {
        valid[ack_index] = false;
        putsUart0("\r\n");
        putsUart0("Acknowledgment received for message with seqID ");
        putnUart0(seqID[ack_index]);
        putsUart0("\r\n");
        goto end;
    }
    else
    {
        UART1_CTL_R |= UART_CTL_TXE;
        UART1_CTL_R &= ~UART_CTL_RXE;

        DEenable = 1;
        index = ack_index;

repeat:

        tx_m = send_Message();

        if(!tx_m)
        {
            timeout = 16384;
            while(timeout)
            timeout--;
            goto repeat;
        }
        else
        {
            while(UART1_FR_R & UART_FR_BUSY);
            DEenable = 0;
            retrans[ack_index]++;
        }

        if(retrans[ack_index]==5)
        {
            ack[ack_index] = 0;
            retrans[ack_index] = 0;
            valid[ack_index] = false;

            putsUart0("\r\n");
            putsUart0("Acknowledgment not received after maximum re try's for message with seqID ");
            putnUart0(seqID[ack_index]);
            putsUart0("\r\n");
            putsUart0("This message is discarded \r\n");
            putsUart0("\r\n");
            putsUart0("    ERROR SENDING MESSAGE:    ");
            putnUart0(seqID[ack_index]);
            putsUart0("\r\n");
            externRED_LED = 1;
        }
        else
            goto again;

            }
end: return;
}

void rx_ack_handle()
{
    uint8_t i = 0;
    uint8_t tx_m;
    while(i<MAX_BUFSIZE)
    {
        if(!valid[i])
        {
            destAdd[i] = rx_source;
            seqID[i] = currentID--;
            cmdNum[i] = 0x70;
            chan[i] = 0;
            size[i] = 1;
            data[i] = rx_seqID;

            UART1_CTL_R |= UART_CTL_TXE;
            UART1_CTL_R &= ~UART_CTL_RXE;
            DEenable = 1;

            index = i;
tryagain:   tx_m = send_Message();

                if(!tx_m)
                {
                    timeout = 16384;
                    while(timeout)
                        timeout--;
                    goto tryagain;
                }

                else
                {
                    while(UART1_FR_R & UART_FR_BUSY);
                    DEenable = 0;
                    break;
                }
        }

        i++;
        if(i==MAX_BUFSIZE)
            putsUart0("sorry, the buffer is full, can't acknowledge the latest message received :( \r\n");
    }
    return;
}


extern void T1ISR(void)
{
    uint8_t decision_tx, decision_rx, i;

        if(in_progress)
            goto transmit;

        if(new_entry)
        {
            store_buffer();
            goto transmit;
        }

        UART1_CTL_R |= UART_CTL_RXE;
        UART1_CTL_R &= ~UART_CTL_TXE;

        if(!DEenable)
            if(!(UART1_FR_R & UART_FR_RXFE) && (phase_tx == 0))
            {
                decision_rx = receive_Message();

                if(decision_rx == 0)
                    goto end;

                else if(decision_rx == 2)
                {
                    phase_rx = 0;
                    goto end;
                }

                else
                {
                    if(verify_checksum == rx_checksum)
                        if(rx_ack == 1)
                        {
                            rx_ack_handle();
                            rx_ack = 0;
                        }
                    perform_task();
                    goto end;
                }
            }

    transmit:

        i = 0;

        if(cs_enable)
            if(!(UART1_FR_R & UART_FR_RXFE))
                goto end;                                        //clear interrupt

        if(phase_rx!=0)
            goto end;

        if(!in_progress)
        {
            while(!valid[i])
            {
                i++;
                if(i>MAX_BUFSIZE)
                    goto end;
            }

            index = i;
            in_progress = true;
            DEenable = 1;
            phase_tx = 0;
        }

        while(in_progress)
        {
            UART1_CTL_R |= UART_CTL_TXE;
            UART1_CTL_R &= ~UART_CTL_RXE;

            decision_tx = send_Message();

            if(!decision_tx)
                goto end;

            else
            {
                while(UART1_FR_R & UART_FR_BUSY);
                DEenable = 0;

                if(ack[index] == 0)
                {
                    valid[index] = false;
                    in_progress = false;
                }
                else
                {
                    ack_index = index;
                    retrans[ack_index] = 1;
                    tx_ack_handle();
                    in_progress = false;
                }
            }

        }

     end:             TIMER1_ICR_R = TIMER_ICR_TATOCINT;

}

//main function
int main(void)
{
    uint8_t i;

    for(i=0;i<=MAX_BUFSIZE;i++)
    {
        valid[i]=false;
        ack[i] = 0;
        ran[i] = 0;
        retrans[i] = 0;
        destAdd[i] = 0;
        size[i] = 0;
        seqID[i] = 0;
        chan[i] = 0;
        cmdNum[i] = 0;
        data[i] = 0;
        DA[i] = 0;
        CH[i] = 0;
    }

    init_hw();

           externGREEN_LED = 1;
           waitMicrosecond(50000);
           externGREEN_LED = 0;

           putsUart0("\r\n");
           putsUart0("............................JYOTHI BHAT...................................... \r\n");
           putsUart0("\r\n");
           putsUart0("                  WELCOME            ");
           putsUart0("This is address  ");
           putnUart0(sourceAdd);
           putsUart0("\r\n");
           putsUart0("                           R E A D Y \r\n");
           putsUart0("\r\n");

    while(1)
    {
askagain:                  putsUart0("enter command:  ");
                           getsUart0(original_string);
                           toLowerCase();
                           transform_string();
                           getCommand();
                           isCommand();
                           if(valid_cmd==false)
                           {
                               BLUE_LED = 1;
                               putsUart0("ERROR: Command or the fields entered is incorrect \r\n");
                               putsUart0("\r\n");
                               new_entry = false;
                               goto askagain;
                           }
                           else
                           {
                               BLUE_LED = 1;
                               waitMicrosecond(50000);
                               BLUE_LED = 0;
                               putsUart0("valid entry \r\n");
                               if(onlymine == true)
                                   goto askagain;
                               new_entry = true;
                           }
    }
}







