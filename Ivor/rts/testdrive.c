#include "test.c"

void shownat(VAL f) {
    switch(f->ty) {
    case FUN:
	printf("FUN %d %d",((function*)(f->info))->ftag,((function*)(f->info))->next);
	break;
    case CON:
	if (TAG(f)==0) printf("O");
	if (TAG(f)==1) {
	    printf("S");
	    shownat(GETCONARG(f,0));
	}
	break;
    case TYPE:
	printf("TYPE");
    }
}

int main()
{
    VAL one;
    VAL two;
    VAL three;
    VAL four,five,six,seven,eight,nine,ten;
    VAL tmp;

    VM_init();

    one = MKCON1(1,MKCON0(0));
    two = MKCON1(1,one);
    three = MKCON1(1,two);
    four = MKCON1(1,three);
    five = MKCON1(1,four);
    six = MKCON1(1,five);
    seven = MKCON1(1,six);
    eight = MKCON1(1,seven);
    nine = MKCON1(1,eight);
    ten = MKCON1(1,nine);

    tmp = _EVM_fact(eight);
    shownat(tmp);
    printf("\n");

    return 0;
}

