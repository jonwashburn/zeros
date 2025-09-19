// Lean compiler output
// Module: rh.Cert.KxiWhitney_RvM
// Imports: Init Mathlib.Data.Real.Basic Mathlib.Data.Nat.Cast.Defs rh.Cert.KxiWhitney rh.Cert.KxiPPlus
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
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_zero;
LEAN_EXPORT lean_object* l_RH_Cert_KxiWhitneyRvM_annularEnergy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Cert_KxiWhitneyRvM_annularEnergy___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_RH_Cert_KxiWhitneyRvM_annularEnergy(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
return x_4;
}
}
LEAN_EXPORT lean_object* l_RH_Cert_KxiWhitneyRvM_annularEnergy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RH_Cert_KxiWhitneyRvM_annularEnergy(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Cast_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_rh_Cert_KxiWhitney(uint8_t builtin, lean_object*);
lean_object* initialize_rh_Cert_KxiPPlus(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_Cert_KxiWhitney__RvM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Cast_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_Cert_KxiWhitney(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_Cert_KxiPPlus(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
