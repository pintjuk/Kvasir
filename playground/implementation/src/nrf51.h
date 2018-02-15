
#ifndef NRF51_H
#define NRF51_H

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

#endif

