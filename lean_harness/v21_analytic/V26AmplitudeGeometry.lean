import Mathlib.Tactic

noncomputable section

namespace HurtadoZeta23

/-- Elementary denominator comparison behind the v26 phase amplitude bound.
No calculus is needed: after cross multiplication the difference is a sum of
three nonnegative products. -/
theorem v26_ratio_amplitude_lower
    {d0 dk x U : ℝ}
    (hd0 : 0 ≤ d0) (hdk : d0 ≤ dk)
    (hx : 0 < x) (hxdk : dk < x ^ 2) (hxU : x ≤ U) :
    U / (U ^ 2 - d0) ≤ x / (x ^ 2 - dk) := by
  have hU : 0 < U := hx.trans_le hxU
  have hxd : 0 < x ^ 2 - dk := sub_pos.mpr hxdk
  have hx2U2 : x ^ 2 ≤ U ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxU) (add_nonneg hx.le hU.le)]
  have hUd : 0 < U ^ 2 - d0 := by
    have : d0 < U ^ 2 := hdk.trans_lt (hxdk.trans_le hx2U2)
    exact sub_pos.mpr this
  apply (div_le_div_iff₀ hUd hxd).2
  have hUx : 0 ≤ U - x := sub_nonneg.mpr hxU
  have h1 : 0 ≤ x * U * (U - x) :=
    mul_nonneg (mul_nonneg hx.le hU.le) hUx
  have h2 : 0 ≤ (U - x) * d0 := mul_nonneg hUx hd0
  have h3 : 0 ≤ U * (dk - d0) :=
    mul_nonneg hU.le (sub_nonneg.mpr hdk)
  nlinarith

/-- Squared form used after the kernel is squared. -/
theorem v26_ratio_amplitude_sq_lower
    {d0 dk x U : ℝ}
    (hd0 : 0 ≤ d0) (hdk : d0 ≤ dk)
    (hx : 0 < x) (hxdk : dk < x ^ 2) (hxU : x ≤ U) :
    U ^ 2 / (U ^ 2 - d0) ^ 2 ≤
      x ^ 2 / (x ^ 2 - dk) ^ 2 := by
  have hrat := v26_ratio_amplitude_lower hd0 hdk hx hxdk hxU
  have hU : 0 < U := hx.trans_le hxU
  have hUd : 0 < U ^ 2 - d0 := by
    have hx2U2 : x ^ 2 ≤ U ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxU) (add_nonneg hx.le hU.le)]
    have : d0 < U ^ 2 := hdk.trans_lt (hxdk.trans_le hx2U2)
    exact sub_pos.mpr this
  have hleft : 0 ≤ U / (U ^ 2 - d0) :=
    div_nonneg hU.le hUd.le
  have hs := pow_le_pow_left₀ hleft hrat 2
  have hxd : (x ^ 2 - dk) ≠ 0 := (sub_pos.mpr hxdk).ne'
  have hUd0 : (U ^ 2 - d0) ≠ 0 := hUd.ne'
  convert hs using 1 <;> field_simp [hxd, hUd0] <;> ring

/-- Adding the nonnegative `c^2` numerator can only increase the exact
amplitude. -/
theorem v26_add_phase_shift_increases_amplitude
    {c dk x : ℝ} (hxdk : dk < x ^ 2) :
    x ^ 2 / (x ^ 2 - dk) ^ 2 ≤
      (x ^ 2 + c ^ 2) / (x ^ 2 - dk) ^ 2 := by
  have hden : 0 < (x ^ 2 - dk) ^ 2 := sq_pos_of_pos (sub_pos.mpr hxdk)
  exact (div_le_div_iff₀ hden hden).2 (by nlinarith [sq_nonneg c])

/-- Full abstract amplitude weakening used by the certificate. -/
theorem v26_amplitude_lower
    {Clo C c d0 dk x U : ℝ}
    (hClo : 0 ≤ Clo) (hC : Clo ≤ C)
    (hd0 : 0 ≤ d0) (hdk : d0 ≤ dk)
    (hx : 0 < x) (hxdk : dk < x ^ 2) (hxU : x ≤ U) :
    Clo ^ 2 * (U ^ 2 / (U ^ 2 - d0) ^ 2) ≤
      C ^ 2 * ((x ^ 2 + c ^ 2) / (x ^ 2 - dk) ^ 2) := by
  have hCnonneg : 0 ≤ C := hClo.trans hC
  have hCsq : Clo ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hClo hC 2
  have hgeom := v26_ratio_amplitude_sq_lower hd0 hdk hx hxdk hxU
  have hshift := v26_add_phase_shift_increases_amplitude (c := c) hxdk
  have hgeom' :
      U ^ 2 / (U ^ 2 - d0) ^ 2 ≤
        (x ^ 2 + c ^ 2) / (x ^ 2 - dk) ^ 2 := hgeom.trans hshift
  have hleft_nonneg : 0 ≤ U ^ 2 / (U ^ 2 - d0) ^ 2 := by positivity
  have hright_nonneg : 0 ≤ (x ^ 2 + c ^ 2) / (x ^ 2 - dk) ^ 2 := by positivity
  calc
    Clo ^ 2 * (U ^ 2 / (U ^ 2 - d0) ^ 2)
        ≤ C ^ 2 * (U ^ 2 / (U ^ 2 - d0) ^ 2) :=
          mul_le_mul_of_nonneg_right hCsq hleft_nonneg
    _ ≤ C ^ 2 * ((x ^ 2 + c ^ 2) / (x ^ 2 - dk) ^ 2) :=
          mul_le_mul_of_nonneg_left hgeom' (sq_nonneg C)

end HurtadoZeta23
