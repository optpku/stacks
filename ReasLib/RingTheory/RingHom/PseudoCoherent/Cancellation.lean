/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.ChangeOfBase
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Basic

/-!
# Cancellation for pseudo-coherent ring maps

Pseudo-coherence of commutative ring maps satisfies cancellation along a pseudo-coherent
intermediate map.
-/

@[expose] public section

universe u v w

namespace RingHom.IsPseudoCoherentRingMap

/-- If a commutative ring map and its composite with a second map are pseudo-coherent, then
the second map is pseudo-coherent. -/
theorem of_comp
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B)
    [f.IsPseudoCoherentRingMap] [(g.comp f).IsPseudoCoherentRingMap] :
    g.IsPseudoCoherentRingMap := sorry

end RingHom.IsPseudoCoherentRingMap
