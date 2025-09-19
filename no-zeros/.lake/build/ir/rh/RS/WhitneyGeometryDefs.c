// Lean compiler output
// Module: rh.RS.WhitneyGeometryDefs
// Imports: Init Mathlib.MeasureTheory.Measure.Lebesgue.Basic Mathlib.MeasureTheory.Integral.SetIntegral Mathlib.Analysis.Convex.Basic
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
lean_object* l_Nat_cast___at_Real_instNatCast___spec__2(lean_object*);
static lean_object* l_RH_RS_Whitney_standardAperture___closed__1;
LEAN_EXPORT lean_object* l_RH_RS_Whitney_standardAperture;
static lean_object* l_RH_RS_Whitney_shadowOverlapConst___closed__1;
LEAN_EXPORT lean_object* l_RH_RS_Whitney_shadowOverlapConst;
static lean_object* _init_l_RH_RS_Whitney_standardAperture___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Nat_cast___at_Real_instNatCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_RH_RS_Whitney_standardAperture() {
_start:
{
lean_object* x_1; 
x_1 = l_RH_RS_Whitney_standardAperture___closed__1;
return x_1;
}
}
static lean_object* _init_l_RH_RS_Whitney_shadowOverlapConst___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = l_Nat_cast___at_Real_instNatCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_RH_RS_Whitney_shadowOverlapConst() {
_start:
{
lean_object* x_1; 
x_1 = l_RH_RS_Whitney_shadowOverlapConst___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Measure_Lebesgue_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Integral_SetIntegral(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Convex_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_RS_WhitneyGeometryDefs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Measure_Lebesgue_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Integral_SetIntegral(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Convex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RH_RS_Whitney_standardAperture___closed__1 = _init_l_RH_RS_Whitney_standardAperture___closed__1();
lean_mark_persistent(l_RH_RS_Whitney_standardAperture___closed__1);
l_RH_RS_Whitney_standardAperture = _init_l_RH_RS_Whitney_standardAperture();
lean_mark_persistent(l_RH_RS_Whitney_standardAperture);
l_RH_RS_Whitney_shadowOverlapConst___closed__1 = _init_l_RH_RS_Whitney_shadowOverlapConst___closed__1();
lean_mark_persistent(l_RH_RS_Whitney_shadowOverlapConst___closed__1);
l_RH_RS_Whitney_shadowOverlapConst = _init_l_RH_RS_Whitney_shadowOverlapConst();
lean_mark_persistent(l_RH_RS_Whitney_shadowOverlapConst);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
