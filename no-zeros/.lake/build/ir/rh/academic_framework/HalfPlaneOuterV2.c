// Lean compiler output
// Module: rh.academic_framework.HalfPlaneOuterV2
// Imports: Init Mathlib.Analysis.Analytic.Basic Mathlib.Data.Complex.Basic Mathlib.Topology.Basic Mathlib.MeasureTheory.Integral.Bochner Mathlib.Analysis.SpecialFunctions.ImproperIntegrals Mathlib.MeasureTheory.Integral.Lebesgue Mathlib.Analysis.SpecialFunctions.Integrals Mathlib.MeasureTheory.Function.AEEqOfIntegral Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan rh.academic_framework.CompletedXi rh.academic_framework.DiskHardy rh.RS.Det2Outer rh.RS.PoissonAI rh.RS.Cayley
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
LEAN_EXPORT lean_object* l_RH_AcademicFramework_HalfPlaneOuterV2__u03a9;
static lean_object* _init_l_RH_AcademicFramework_HalfPlaneOuterV2__u03a9() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Analytic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Complex_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Integral_Bochner(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_ImproperIntegrals(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Integral_Lebesgue(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Integrals(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Function_AEEqOfIntegral(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Arctan(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_CompletedXi(uint8_t builtin, lean_object*);
lean_object* initialize_rh_academic__framework_DiskHardy(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_Det2Outer(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_PoissonAI(uint8_t builtin, lean_object*);
lean_object* initialize_rh_RS_Cayley(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_academic__framework_HalfPlaneOuterV2(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Analytic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Integral_Bochner(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_ImproperIntegrals(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Integral_Lebesgue(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Integrals(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Function_AEEqOfIntegral(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Arctan(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_CompletedXi(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_academic__framework_DiskHardy(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_Det2Outer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_PoissonAI(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_rh_RS_Cayley(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RH_AcademicFramework_HalfPlaneOuterV2__u03a9 = _init_l_RH_AcademicFramework_HalfPlaneOuterV2__u03a9();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
