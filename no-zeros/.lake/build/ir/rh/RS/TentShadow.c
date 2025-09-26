// Lean compiler output
// Module: rh.RS.TentShadow
// Imports: Init Mathlib.Data.Real.Basic Mathlib.Topology.Instances.Real Mathlib.Topology.Instances.Complex rh.RS.CRGreenOuter Mathlib.MeasureTheory.Integral.SetIntegral Mathlib.Topology.Algebra.FilterBasis Mathlib.MeasureTheory.Function.Egorov Mathlib.MeasureTheory.Covering.Differentiation Mathlib.MeasureTheory.Measure.Lebesgue.Basic Mathlib.MeasureTheory.Covering.Besicovitch rh.Cert.KxiPPlus Mathlib.Analysis.SpecificLimits.Basic
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Instances_Real(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Instances_Complex(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_CRGreenOuter(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Integral_SetIntegral(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Algebra_FilterBasis(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Function_Egorov(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Covering_Differentiation(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Measure_Lebesgue_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Covering_Besicovitch(uint8_t builtin, lean_object*);
lean_object* initialize_rh_Cert_KxiPPlus(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecificLimits_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_RS_TentShadow(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Instances_Real(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Instances_Complex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_CRGreenOuter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Integral_SetIntegral(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Algebra_FilterBasis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Function_Egorov(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Covering_Differentiation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Measure_Lebesgue_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Covering_Besicovitch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_Cert_KxiPPlus(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecificLimits_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
