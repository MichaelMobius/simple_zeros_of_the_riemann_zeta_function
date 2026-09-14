import HurtadoZeta23.V26BootstrapStageLists
import Mathlib.Tactic

namespace HurtadoZeta23

/-- The published six-digit decimal encoding is injective on the bounded
A-B-C-C-B-A basin-word type.  This lets later bootstrap dispatch layers reason
on compact Nat code tables and recover the unique concrete basin word only
when entering a per-word certificate. -/
theorem v26_wordCode_injective : Function.Injective v26WordCode := by
  intro x y hcode
  rcases x with ⟨a, b, c, d, e, f⟩
  rcases y with ⟨a', b', c', d', e', f'⟩
  have ha_lt := a.isLt
  have hb_lt := b.isLt
  have hc_lt := c.isLt
  have hd_lt := d.isLt
  have he_lt := e.isLt
  have hf_lt := f.isLt
  have ha'_lt := a'.isLt
  have hb'_lt := b'.isLt
  have hc'_lt := c'.isLt
  have hd'_lt := d'.isLt
  have he'_lt := e'.isLt
  have hf'_lt := f'.isLt
  simp [v26WordCode] at hcode
  have ha_val : a.val = a'.val := by omega
  have hb_val : b.val = b'.val := by omega
  have hc_val : c.val = c'.val := by omega
  have hd_val : d.val = d'.val := by omega
  have he_val : e.val = e'.val := by omega
  have hf_val : f.val = f'.val := by omega
  have ha : a = a' := Fin.ext ha_val
  have hb : b = b' := Fin.ext hb_val
  have hc : c = c' := Fin.ext hc_val
  have hd : d = d' := Fin.ext hd_val
  have he : e = e' := Fin.ext he_val
  have hf : f = f' := Fin.ext hf_val
  simp [ha, hb, hc, hd, he, hf]

end HurtadoZeta23
