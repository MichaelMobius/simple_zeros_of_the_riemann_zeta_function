import HurtadoZeta23.V26PhaseUpper
import HurtadoZeta23.V26SineChord
import HurtadoZeta23.V26AmplitudeGeometry
import HurtadoZeta23.V26PhaseConstants
import HurtadoZeta23.V26PhaseIdentity
import HurtadoZeta23.V26IntervalGeometry
import HurtadoZeta23.V26PhasePeriodicity
import HurtadoZeta23.V26PhaseRationalBounds

noncomputable section

namespace HurtadoZeta23

/-- Marker theorem: importing this module forces Lean to kernel-check every
analytic prerequisite for the rational phase minorant. -/
theorem v26_minorant_prereqs_loaded : True := by trivial

end HurtadoZeta23
