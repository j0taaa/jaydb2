/* Test-only real-driver forwarding: launch attestation and deterministic faults.
 * No fabricated GPU result: successful calls always go to libcuda.
 */
#define _GNU_SOURCE
#include <cuda.h>
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fault(const char *kind) {
  const char *path = getenv("JAYDB_TEST_GPU_FAULT");
  char value[32] = {0};
  FILE *f = path ? fopen(path, "r") : NULL;
  if (f) { (void)fread(value, 1, sizeof(value)-1, f); fclose(f); }
  return !strcmp(value, kind);
}
static void note(const char *event, CUresult result) {
  const char *path = getenv("JAYDB_TEST_GPU_TRACE");
  FILE *f = path ? fopen(path, "a") : NULL;
  if (f) { fprintf(f, "%s %d\n", event, (int)result); fclose(f); }
}
/* Test-owned indirection allows selecting the prepared bundle after startup. */
static void tamper(int key) {
  const char *name = getenv("JAYDB_TEST_GPU_BUNDLE_PATH");
  char path[4096] = {0};
  FILE *list = name ? fopen(name, "r") : NULL;
  if (!list) return;
  (void)fread(path, 1, sizeof(path)-1, list); fclose(list);
  FILE *bundle = fopen(path, "r+b");
  if (!bundle) return;
  if (key) { unsigned long long zero = 0; (void)fwrite(&zero, 1, 8, bundle); }
  else { (void)fseek(bundle, 8, SEEK_SET); int c = fgetc(bundle);
    if (c != EOF) { (void)fseek(bundle, 8, SEEK_SET); (void)fputc(c ^ 1, bundle); } }
  fclose(bundle);
}
CUresult cuInit(unsigned int flags) {
  CUresult (*real)(unsigned int) = dlsym(RTLD_NEXT, "cuInit");
  CUresult r = fault("device") ? CUDA_ERROR_NO_DEVICE : real(flags);
  if (r == CUDA_SUCCESS && fault("rebuild")) tamper(1);
  note("init", r); return r;
}
CUresult cuMemAllocManaged(CUdeviceptr *p, size_t n, unsigned int flags) {
  CUresult (*real)(CUdeviceptr *, size_t, unsigned int) = dlsym(RTLD_NEXT, "cuMemAllocManaged");
  CUresult r = fault("allocation") ? CUDA_ERROR_OUT_OF_MEMORY : real(p, n, flags);
  note("allocation", r); return r;
}
static int launched;
static int tampered;
CUresult cuLaunchKernel(CUfunction fn, unsigned int gx, unsigned int gy, unsigned int gz,
  unsigned int bx, unsigned int by, unsigned int bz, unsigned int shared, CUstream stream,
  void **args, void **extra) {
  CUresult (*real)(CUfunction, unsigned int, unsigned int, unsigned int, unsigned int,
    unsigned int, unsigned int, unsigned int, CUstream, void **, void **) = dlsym(RTLD_NEXT, "cuLaunchKernel");
  CUresult r = fault("launch") ? CUDA_ERROR_LAUNCH_FAILED : real(fn, gx, gy, gz, bx, by, bz, shared, stream, args, extra);
  launched = 1; note("launch", r); return r;
}
CUresult cuCtxSynchronize(void) {
  CUresult (*real)(void) = dlsym(RTLD_NEXT, "cuCtxSynchronize");
  CUresult r = real();
  if (r == CUDA_SUCCESS && launched && fault("runtime")) r = CUDA_ERROR_ILLEGAL_ADDRESS;
  if (r == CUDA_SUCCESS && launched && !tampered && fault("changed")) {
    tamper(0); tampered = 1;
  }
  note("sync", r); return r;
}
