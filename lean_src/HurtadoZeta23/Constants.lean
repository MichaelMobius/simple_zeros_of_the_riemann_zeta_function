import Zeta23.ThmD.Mult

noncomputable section

namespace HurtadoZeta23

/-- The Montgomery--Taylor baseline, using exactly Anthropic/Zeta23's definition. -/
def HMT : ℝ := Zeta23.ThmD.HD 1

/-- Certified seven-point local lower bound. -/
def delta : ℝ := 39 / 10000

/-- Total pressure. -/
def beta : ℝ := 1 / 500

/-- Shifted-block length. -/
def blockLength : ℕ := 262

/-- A₀ = δ (m-6). -/
def A0 : ℝ := delta * (blockLength - 6)

/-- Coefficient of N₀ˢ after shifted-block averaging. -/
def alpha : ℝ := 312 / 81875

/-- Global pressure cost multiplying N. -/
def pressureCost : ℝ := 261 / 131000

/-- Coefficient remaining on the left after moving α N₀ˢ. -/
def oneMinusAlpha : ℝ := 81563 / 81875

/-- Constant stated in the paper. -/
def publishedConstant : ℝ := (655000 * HMT - 1305) / 652504

lemma A0_eq : A0 = 624 / 625 := by
  norm_num [A0, delta, blockLength]

/-- Fixed endpoint loss in shifted block averaging. -/
def endpointCorrection : ℝ :=
  A0 * ((blockLength - 1 : ℕ) : ℝ) / blockLength

lemma endpointCorrection_nonneg :
    0 ≤ endpointCorrection := by
  unfold endpointCorrection
  rw [A0_eq]
  norm_num [blockLength]

lemma A0_lt_one : A0 < 1 := by
  rw [A0_eq]
  norm_num

lemma alpha_eq_A0_div_m : alpha = A0 / blockLength := by
  rw [A0_eq]
  norm_num [alpha, blockLength]

lemma pressureCost_eq :
    pressureCost = ((blockLength - 1 : ℕ) : ℝ) / (500 * (blockLength : ℝ)) := by
  norm_num [pressureCost, blockLength]

lemma oneMinusAlpha_eq : 1 - alpha = oneMinusAlpha := by
  norm_num [alpha, oneMinusAlpha]

lemma oneMinusAlpha_pos : 0 < 1 - alpha := by
  norm_num [alpha]

lemma publishedConstant_eq_ratio :
    publishedConstant = (HMT - pressureCost) / (1 - alpha) := by
  unfold publishedConstant pressureCost alpha
  field_simp
  ring

end HurtadoZeta23
