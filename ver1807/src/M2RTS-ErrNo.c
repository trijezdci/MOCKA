#include <errno.h>

int ErrNo(void) {
	return __errno_location;
}
