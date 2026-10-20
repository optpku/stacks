/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

@[expose] public section

/-!
# Stalks of a scheme normalization

This leaf names the stalk of the pushed-forward normalization structure sheaf,
its canonical map from the source stalk, and the total-quotient-ring objects
used to compare it with an integral closure.
-/

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Normalization.Stalk

variable (X : Scheme.{u})
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

/-- The stalk of `ν_*𝒪_{X^ν}` at `x`, where `ν : X.normalization ⟶ X`. -/
noncomputable abbrev pushforward (x : X) : Type u :=
  ((((TopCat.Sheaf.pushforward CommRingCat X.normalizationTo.base).obj
      X.normalization.sheaf).presheaf).stalk x)

/-- The canonical map `𝒪_{X, x} → (ν_*𝒪_{X^ν})_x` on normalization stalks. -/
noncomputable def pushforwardMap (x : X) :
    X.presheaf.stalk x →+* pushforward X x :=
  (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (RingedSpace.Hom.commRingSheafPushforwardMap X.normalizationTo.toShHom).hom).hom)

/-- The normalization pushforward stalk is canonically an algebra over the source stalk. -/
noncomputable instance instPushforwardAlgebra (x : X) :
    Algebra (X.presheaf.stalk x) (pushforward X x) :=
  (pushforwardMap X x).toAlgebra

/-- The total quotient ring of the reduction of the local ring `𝒪_{X, x}`. -/
noncomputable abbrev reducedTotalQuotient (x : X) : Type u :=
  Localization (nonZeroDivisors (X.presheaf.stalk x ⧸ _root_.nilradical (X.presheaf.stalk x)))

/-- The map from `𝒪_{X, x}` to the total quotient ring of its reduction. -/
noncomputable def reducedTotalQuotientMap (x : X) :
    X.presheaf.stalk x →+* reducedTotalQuotient X x :=
  ((algebraMap
      (X.presheaf.stalk x ⧸ _root_.nilradical (X.presheaf.stalk x))
      (reducedTotalQuotient X x)).comp
    (algebraMap (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ _root_.nilradical (X.presheaf.stalk x))))

namespace Reduction

/-- The total quotient ring of the reduced source stalk is canonically an algebra over the source
stalk. -/
noncomputable instance instTotalQuotientAlgebra (x : X) :
    Algebra (X.presheaf.stalk x) (reducedTotalQuotient X x) :=
  (reducedTotalQuotientMap X x).toAlgebra

end Reduction

/-- The integral closure of `𝒪_{X, x}` in the total quotient ring of its reduction. -/
noncomputable abbrev reducedIntegralClosure (x : X) : Type u :=
  integralClosure (X.presheaf.stalk x) (reducedTotalQuotient X x)

end AlgebraicGeometry.Scheme.Normalization.Stalk
