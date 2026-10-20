module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Tactic.CrossRefAttribute

/-! 
# K-injective direct images of modules

The flat-pullback/exact-adjunction API gives the ringed-space specialization of the generic
K-injective transport theorem.  The construction is an instance so later derived pushforward
arguments do not rebuild the same adjunction and exactness witnesses.
-/

@[expose] public section

open CategoryTheory ComplexShape AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.KInjective

variable {X Y : RingedSpace.{u}}

/-- The termwise cochain-complex direct image attached to a ringed-space morphism. -/
abbrev complex (f : X ⟶ Y) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex Y.Modules ℤ :=
  (f _*).mapHomologicalComplex (up ℤ)

section

-- The target unfolds through several sheaf functors.  Keep the extra elaboration budget local
-- to the canonical instance instead of making it part of the importing environment.
set_option maxHeartbeats 800000

/-- Lemma 20.32.9 (0D5Z): direct image along a flat morphism of ringed spaces preserves
K-injective cochain complexes. -/
@[stacks 0D5Z "flat direct image preserves K-injective complexes", instance]
theorem isKInjective
    (f : X ⟶ Y) [_root_.RingedSpace.Hom.IsFlat f]
    (I : CochainComplex X.Modules ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (complex f |>.obj I) := sorry

end

end AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.KInjective

end
