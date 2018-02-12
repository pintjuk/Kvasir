#define UART_BASE       0x40002000
#define UART_STARTRX    (UART_BASE+0x000)
#define UART_STOPRX     (UART_BASE+0x004)
#define UART_STARTTX    (UART_BASE+0x008)
#define UART_STOPTX     (UART_BASE+0x00C)
#define UART_RXREADY    (UART_BASE+0x108)
#define UART_TXREADY    (UART_BASE+0x11C)
#define UART_ENABLE     (UART_BASE+0x500)
#define UART_PSELTXD    (UART_BASE+0x50C)
#define UART_PSELRXD    (UART_BASE+0x514)
#define UART_RXD        (UART_BASE+0x518)
#define UART_TXD        (UART_BASE+0x51C)
#define UART_BAUDRATE   (UART_BASE+0x524)
#define UART_CONFIG     (UART_BASE+0x56C)


#define GET32( a ) ((*(volatile unsigned int*) a))
#define PUT32( a, v ) ((*(volatile unsigned int*) a) = v)


void delay(unsigned int x) {
  while (x > 0) {
    asm("");
    x--;
  };
}

void uart_init ()
{
    //PUT32(UART_BAUDRATE,0x01D7E000); //115200
    PUT32(UART_BAUDRATE,0x00EBF000); //57600
    //PUT32(UART_BAUDRATE,0x00275000); //9600
    //PUT32(UART_PSELTXD,24); // USB
    PUT32(UART_PSELRXD,25); // USB
    PUT32(UART_PSELTXD,2); // Pad 1
    //PUT32(UART_PSELRXD,2); // Pad 2
    PUT32(UART_ENABLE,4);
    PUT32(UART_STARTTX,1);
    PUT32(UART_STARTRX,1);

    // some magic that I don't understand yet
    PUT32(UART_TXD,0x00);
    delay(0x1000);
}

void uart_send ( unsigned int x )
{
    while(GET32(UART_TXREADY)==0) continue;
    PUT32(UART_TXREADY,0);
    PUT32(UART_TXD,x);
}


void uart_send_string ( char *s )
{
  while(*s != 0) {
    uart_send(*s);
    s++;
  }
}


unsigned int uart_read ( )
{
    while (GET32(UART_RXREADY)==0) continue;
    PUT32(UART_RXREADY,0);
    return GET32(UART_RXD);
}