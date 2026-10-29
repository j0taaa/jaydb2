#include <node.h>
#include <v8.h>
#include <cstdint>

// Public V8 API, using its full uintptr_t address domain. No int32 KiB
// multiplication and no language recursion quota. Linux grows the main
// stack; the host observes its allocations and enforces the public deadline.
NODE_MODULE_INIT() {
  static_assert(sizeof(uintptr_t) == 8, "Linux x86_64 address domain required");
  // This is an address, not a byte budget. The deployment's first mappable
  // user address is >=64 KiB (checked by the host launcher). This also leaves
  // room for V8 24's central-stack view's 40 KiB safety margin, whose unsigned
  // subtraction would underflow with a limit of 0 or 1.
  v8::Isolate::GetCurrent()->SetStackLimit(uintptr_t{65536});
}
