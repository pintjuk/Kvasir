#ifndef DRIVER_H
#define DRIVER_H


void uart_init ();
void uart_send ( unsigned int x );
void uart_send_string ( char *s );
unsigned int uart_read ( );

#endif
