// Lean compiler output
// Module: rh.academic_framework.CayleyAdapters
// Imports: Init rh.academic_framework.DiskHardy rh.academic_framework.HalfPlaneOuterV2
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_RH_AcademicFramework_CayleyAdapters_b(lean_object*);
LEAN_EXPORT lean_object* l_RH_AcademicFramework_CayleyAdapters_b___boxed(lean_object*);
LEAN_EXPORT lean_object* l_RH_AcademicFramework_CayleyAdapters_b(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_RH_AcademicFramework_CayleyAdapters_b___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RH_AcademicFramework_CayleyAdapters_b(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_DiskHardy(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_HalfPlaneOuterV2(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_academic__framework_CayleyAdapters(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_DiskHardy(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_HalfPlaneOuterV2(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
