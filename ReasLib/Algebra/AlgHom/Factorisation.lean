/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Category.Factorisation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.AlgHom.ULift

@[expose] public section

/-!
# Factorisations of algebra homomorphisms

This is the algebra-map-facing, cross-universe view of mathlib's categorical
`CategoryTheory.Factorisation`.
-/

open CategoryTheory

universe u v w x

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- A categorical factorisation of an algebra homomorphism, with its source
and target lifted to the universe containing the base and both endpoints. -/
abbrev Factorisation (f : A →ₐ[R] B) :=
  CategoryTheory.Factorisation (CommAlgCat.ofHom f.uliftMap)

namespace Factorisation

variable {f : A →ₐ[R] B}

/-- A factorisation of an algebra map through a specified intermediate
algebra. Unlike `AlgHom.Factorisation`, the midpoint universe remains an
explicit input, so this form can retain source data from an independent
universe. -/
@[stacks 07F0 "factorisation through a specified algebra"]
structure Through (f : A →ₐ[R] B) (M : Type x) [CommRing M] [Algebra R M] where
  /-- The map from the source to the specified intermediate algebra. -/
  fromSource : A →ₐ[R] M
  /-- The map from the specified intermediate algebra to the target. -/
  toTarget : M →ₐ[R] B
  /-- The two maps compose to the original algebra map. -/
  factor : toTarget.comp fromSource = f

namespace Through

variable {M : Type x} [CommRing M] [Algebra R M]

/-- Build a factorisation through a specified algebra from its two maps and
triangle equation. -/
def ofMaps (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f) : Through f M :=
  { fromSource := fromSource
    toTarget := toTarget
    factor := factor }

end Through

/-- The lifted categorical triangle used by `Factorisation.ofMaps`. -/
theorem ofMaps_comp {M : Type (max u v w)} [CommRing M] [Algebra R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f) :
    CommAlgCat.ofHom (fromSource.comp ULift.algEquiv.toAlgHom) ≫
        CommAlgCat.ofHom (ULift.algEquiv.symm.toAlgHom.comp toTarget) =
      CommAlgCat.ofHom f.uliftMap := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  change ULift.up (toTarget (fromSource a.down)) = ULift.up (f a.down)
  exact congrArg ULift.up (DFunLike.congr_fun factor a.down)

/-- Build a bundled algebra-homomorphism factorisation from its midpoint,
two maps, and their factorisation equation. -/
noncomputable def ofMaps {M : Type (max u v w)} [CommRing M] [Algebra R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f) : f.Factorisation where
  mid := CommAlgCat.of R M
  ι := CommAlgCat.ofHom (fromSource.comp ULift.algEquiv.toAlgHom)
  π := CommAlgCat.ofHom (ULift.algEquiv.symm.toAlgHom.comp toTarget)
  ι_π := ofMaps_comp fromSource toTarget factor

/-- The map from the source to the midpoint of an algebra-homomorphism
factorisation. -/
noncomputable def fromSource (F : f.Factorisation) : A →ₐ[R] F.mid :=
  F.ι.hom.comp ULift.algEquiv.symm.toAlgHom

/-- The map from the midpoint to the original, unlifted target. -/
noncomputable def toTarget (F : f.Factorisation) : F.mid →ₐ[R] B :=
  ULift.algEquiv.toAlgHom.comp F.π.hom

/-- The two map-facing projections of an algebra-homomorphism factorisation
compose to the original map. -/
theorem factor (F : f.Factorisation) :
    F.toTarget.comp F.fromSource = f := by
  apply AlgHom.ext
  intro a
  exact congrArg ULift.down
    (DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom F.ι_π) (ULift.up a))

/-! A finite-presentation wrapper keeps the midpoint instance attached to the
factorisation witness.  This is the reusable form used by prime-local
resolution criteria. -/

/-- A factorisation whose midpoint is finitely presented over the base ring. -/
structure Finite (f : A →ₐ[R] B) where
  /-- The underlying categorical factorisation. -/
  base : AlgHom.Factorisation f
  /-- Finite presentation of the midpoint, retained as an instance. -/
  [finitePresentation : Algebra.FinitePresentation R base.mid]

attribute [instance] Finite.finitePresentation

namespace Finite

variable {f : A →ₐ[R] B}

/-- The midpoint of a finite-presentation factorisation. -/
abbrev mid (F : Finite f) := F.base.mid

/-- The source map of a finite-presentation factorisation. -/
noncomputable abbrev fromSource (F : Finite f) : A →ₐ[R] F.mid :=
  F.base.fromSource

/-- The target map of a finite-presentation factorisation. -/
noncomputable abbrev toTarget (F : Finite f) : F.mid →ₐ[R] B :=
  F.base.toTarget

/-- The factorisation equation carried by a finite-presentation factorisation. -/
theorem factor (F : Finite f) :
    F.toTarget.comp F.fromSource = f := F.base.factor

/-- The finite-presentation and triangle laws carried by a finite factorisation. -/
theorem spec (F : Finite f) :
    Algebra.FinitePresentation R F.mid ∧
      F.toTarget.comp F.fromSource = f := ⟨inferInstance, F.factor⟩

/-- Attach a finite-presentation instance to an existing factorisation. -/
def of (F : AlgHom.Factorisation f) [Algebra.FinitePresentation R F.mid] :
    Finite f :=
  { base := F }

/-- Build a finite-presentation factorisation directly from two algebra maps. -/
noncomputable def ofMaps {M : Type (max u v w)} [CommRing M] [Algebra R M]
    [Algebra.FinitePresentation R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f) : Finite f :=
  { base := Factorisation.ofMaps fromSource toTarget factor
    -- The categorical midpoint is definitionally `M`; this explicit field
    -- assignment transports its existing finite-presentation fact.
    finitePresentation := inferInstanceAs (Algebra.FinitePresentation R M) }

/-- The canonical finite factorisation of a map through the common-universe
lift of its source. -/
noncomputable def initial (f : A →ₐ[R] B) [Algebra.FinitePresentation R A] :
    Finite f where
  base := CategoryTheory.Factorisation.initial
  finitePresentation := Algebra.FinitePresentation.equiv
    (ULift.algEquiv.symm : A ≃ₐ[R] ULift.{max u w} A)

/-- Precomposing the source map of a finite factorisation preserves its
triangle law. -/
theorem precomp_factor {C : Type (max u v w)} [CommRing C] [Algebra R C]
    (F : Finite f) (h : C →ₐ[R] A) :
    F.toTarget.comp (F.fromSource.comp h) = f.comp h := by
  rw [← AlgHom.comp_assoc, F.factor]

/-- Precompose a finite factorisation while retaining its finitely presented
midpoint and target map. -/
noncomputable def precomp {C : Type (max u v w)} [CommRing C] [Algebra R C]
    (F : Finite f) (h : C →ₐ[R] A) : Finite (f.comp h) :=
  Finite.ofMaps (F.fromSource.comp h) F.toTarget (precomp_factor F h)

/-- Forgetting the finite-presentation wrapper recovers the underlying
categorical factorisation. -/
@[simp]
theorem base_of (F : AlgHom.Factorisation f) [Algebra.FinitePresentation R F.mid] :
    (Finite.of F).base = F := rfl

/-- The source map supplied to `Finite.ofMaps` is recovered by projection. -/
@[simp]
theorem fromSource_ofMaps {M : Type (max u v w)} [CommRing M] [Algebra R M]
    [Algebra.FinitePresentation R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f) :
    (Finite.ofMaps fromSource toTarget factor).fromSource = fromSource := rfl

/-- The target map supplied to `Finite.ofMaps` is recovered by projection. -/
@[simp]
theorem toTarget_ofMaps {M : Type (max u v w)} [CommRing M] [Algebra R M]
    [Algebra.FinitePresentation R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f) :
    (Finite.ofMaps fromSource toTarget factor).toTarget = toTarget := rfl

/-- The canonical finite factorisation uses the universe-lift equivalence as
its source map. -/
@[simp]
theorem fromSource_initial (f : A →ₐ[R] B) [Algebra.FinitePresentation R A] :
    (Finite.initial f).fromSource =
      (ULift.algEquiv.symm : A ≃ₐ[R] ULift.{max u w} A).toAlgHom := rfl

/-- The target map of the canonical finite factorisation lowers its midpoint
before applying the original map. -/
@[simp]
theorem toTarget_initial (f : A →ₐ[R] B) [Algebra.FinitePresentation R A] :
    (Finite.initial f).toTarget =
      f.comp (ULift.algEquiv : ULift.{max u w} A ≃ₐ[R] A).toAlgHom := rfl

/-- Precomposition composes the supplied map onto the source projection. -/
@[simp]
theorem fromSource_precomp {C : Type (max u v w)} [CommRing C] [Algebra R C]
    (F : Finite f) (h : C →ₐ[R] A) :
    (F.precomp h).fromSource = F.fromSource.comp h := rfl

/-- Precomposition leaves the target projection unchanged. -/
@[simp]
theorem toTarget_precomp {C : Type (max u v w)} [CommRing C] [Algebra R C]
    (F : Finite f) (h : C →ₐ[R] A) :
    (F.precomp h).toTarget = F.toTarget := rfl

end Finite

/-! Smoothness is canonical structure on the midpoint, so it is retained in a
wrapper whose instance projection is available after unpacking a witness. -/

/-- A factorisation whose midpoint is smooth over the base ring. -/
structure Smooth (f : A →ₐ[R] B) where
  /-- The underlying categorical factorisation. -/
  base : AlgHom.Factorisation f
  /-- Smoothness of the midpoint, retained as an instance. -/
  [smooth : Algebra.Smooth R base.mid]

attribute [instance] Smooth.smooth

namespace Smooth

variable {f : A →ₐ[R] B}

/-- The smooth midpoint of a smooth factorisation. -/
abbrev mid (F : Smooth f) := F.base.mid

/-- The source map of a smooth factorisation. -/
noncomputable abbrev fromSource (F : Smooth f) : A →ₐ[R] F.mid :=
  F.base.fromSource

/-- The target map of a smooth factorisation. -/
noncomputable abbrev toTarget (F : Smooth f) : F.mid →ₐ[R] B :=
  F.base.toTarget

/-- The triangle law carried by a smooth factorisation. -/
theorem factor (F : Smooth f) :
    F.toTarget.comp F.fromSource = f := F.base.factor

/-- The smoothness and triangle law carried by a smooth factorisation. -/
theorem spec (F : Smooth f) :
    Algebra.Smooth R F.mid ∧ F.toTarget.comp F.fromSource = f := ⟨inferInstance, F.factor⟩

/-- Attach midpoint smoothness to an existing factorisation. -/
def of (F : AlgHom.Factorisation f) [Algebra.Smooth R F.mid] : Smooth f :=
  { base := F }

/-- Build a smooth factorisation directly from two algebra maps. -/
noncomputable def ofMaps {M : Type (max u v w)} [CommRing M] [Algebra R M]
    [Algebra.Smooth R M] (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f) : Smooth f :=
  { base := Factorisation.ofMaps fromSource toTarget factor
    smooth := inferInstanceAs (Algebra.Smooth R M) }

/-- A smooth factorisation is, in particular, a finite-presentation
factorisation. -/
def toFinite (F : Smooth f) : Finite f :=
  { base := F.base
    finitePresentation := inferInstanceAs (Algebra.FinitePresentation R F.mid) }

/-- The source map supplied to `Smooth.ofMaps` is recovered by projection. -/
@[simp]
theorem fromSource_ofMaps {M : Type (max u v w)} [CommRing M] [Algebra R M]
    [Algebra.Smooth R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f) :
    (Smooth.ofMaps fromSource toTarget factor).fromSource = fromSource := rfl

/-- The target map supplied to `Smooth.ofMaps` is recovered by projection. -/
@[simp]
theorem toTarget_ofMaps {M : Type (max u v w)} [CommRing M] [Algebra R M]
    [Algebra.Smooth R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f) :
    (Smooth.ofMaps fromSource toTarget factor).toTarget = toTarget := rfl

/-- Forgetting smoothness preserves the source map. -/
@[simp]
theorem fromSource_toFinite (F : Smooth f) :
    F.toFinite.fromSource = F.fromSource := rfl

/-- Forgetting smoothness preserves the target map. -/
@[simp]
theorem toTarget_toFinite (F : Smooth f) :
    F.toFinite.toTarget = F.toTarget := rfl

end Smooth

/-- The source map of a factorisation built by `ofMaps`. -/
@[simp]
theorem fromSource_ofMaps {M : Type (max u v w)} [CommRing M] [Algebra R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f) :
    (ofMaps fromSource toTarget factor).fromSource = fromSource := rfl

/-- The target map of a factorisation built by `ofMaps`. -/
@[simp]
theorem toTarget_ofMaps {M : Type (max u v w)} [CommRing M] [Algebra R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f) :
    (ofMaps fromSource toTarget factor).toTarget = toTarget := rfl

end Factorisation

/-! A quotient factorisation remembers a presentation of its midpoint as an
explicit quotient.  This is data beyond an ordinary categorical
`Factorisation`, and is useful independently of any smoothness hypothesis. -/

/-- A factorisation of an algebra homomorphism through an explicitly presented
quotient algebra. The prequotient lies in the common universe of the base and
endpoints so that `toFactorisation` needs no additional universe transport. -/
structure QuotientFactorisation (f : A →ₐ[R] B) where
  /-- The algebra before taking the quotient. -/
  prequotient : Type (max u v w)
  /-- The commutative-ring structure on the prequotient algebra. -/
  instCommRing : CommRing prequotient
  /-- The algebra structure on the prequotient algebra. -/
  instAlgebra : Algebra R prequotient
  /-- The ideal defining the midpoint quotient. -/
  ideal : Ideal prequotient
  /-- The map from the source to the quotient midpoint. -/
  fromSource : A →ₐ[R] prequotient ⧸ ideal
  /-- The map from the quotient midpoint to the target. -/
  toTarget : prequotient ⧸ ideal →ₐ[R] B
  /-- The quotient midpoint factors the original map. -/
  factor : toTarget.comp fromSource = f

attribute [instance] QuotientFactorisation.instCommRing
  QuotientFactorisation.instAlgebra

namespace QuotientFactorisation

variable {f : A →ₐ[R] B}

/-- The actual midpoint of a quotient factorisation. -/
abbrev mid (F : QuotientFactorisation f) := F.prequotient ⧸ F.ideal

/-- Forget the explicit quotient presentation and obtain the ordinary
categorical factorisation of the same algebra map. -/
noncomputable def toFactorisation (F : QuotientFactorisation f) : f.Factorisation :=
  Factorisation.ofMaps F.fromSource F.toTarget F.factor

/-- The source map is preserved by `toFactorisation`. -/
@[simp]
theorem fromSource_toFactorisation (F : QuotientFactorisation f) :
    F.toFactorisation.fromSource = F.fromSource := rfl

/-- The target map is preserved by `toFactorisation`. -/
@[simp]
theorem toTarget_toFactorisation (F : QuotientFactorisation f) :
    F.toFactorisation.toTarget = F.toTarget := rfl

/-- Build a quotient factorisation from its prequotient algebra, ideal, and
two algebra maps. -/
def ofMaps {P : Type (max u v w)} [CommRing P] [Algebra R P]
    (J : Ideal P) (fromSource : A →ₐ[R] P ⧸ J)
    (toTarget : P ⧸ J →ₐ[R] B) (factor : toTarget.comp fromSource = f) :
    QuotientFactorisation f :=
  { prequotient := P
    instCommRing := inferInstance
    instAlgebra := inferInstance
    ideal := J
    fromSource := fromSource
    toTarget := toTarget
    factor := factor }

/-- The ideal of a quotient factorisation built by `ofMaps` is the supplied
ideal. -/
@[simp]
theorem ideal_ofMaps {P : Type (max u v w)} [CommRing P] [Algebra R P]
    (J : Ideal P) (fromSource : A →ₐ[R] P ⧸ J)
    (toTarget : P ⧸ J →ₐ[R] B) (factor : toTarget.comp fromSource = f) :
    (ofMaps J fromSource toTarget factor).ideal = J := rfl

/-- The source map of a quotient factorisation built by `ofMaps` is the
supplied map. -/
@[simp]
theorem fromSource_ofMaps
    {P : Type (max u v w)} [CommRing P] [Algebra R P]
    (J : Ideal P) (fromSource : A →ₐ[R] P ⧸ J)
    (toTarget : P ⧸ J →ₐ[R] B) (factor : toTarget.comp fromSource = f) :
    (ofMaps J fromSource toTarget factor).fromSource = fromSource := rfl

/-- The target map of a quotient factorisation built by `ofMaps` is the
supplied map. -/
@[simp]
theorem toTarget_ofMaps
    {P : Type (max u v w)} [CommRing P] [Algebra R P]
    (J : Ideal P) (fromSource : A →ₐ[R] P ⧸ J)
    (toTarget : P ⧸ J →ₐ[R] B) (factor : toTarget.comp fromSource = f) :
    (ofMaps J fromSource toTarget factor).toTarget = toTarget := rfl

end QuotientFactorisation

/-! A cospan has two source maps and therefore deserves a separate owner from
   the single-source `Factorisation` above. -/

/-- A common factorisation of two algebra maps with the same target. -/
@[stacks 07CT "common factorisation of algebra maps"]
structure CommonFactorisation
    {R : Type u} {A : Type v} {D : Type w} {B : Type x}
    [CommRing R] [CommRing A] [CommRing D] [CommRing B]
    [Algebra R A] [Algebra R D] [Algebra R B]
    (fLeft : A →ₐ[R] B) (fRight : D →ₐ[R] B) where
  /-- The common intermediate algebra. -/
  mid : Type (max (max u v) (max w x))
  /-- The commutative-ring structure on the intermediate algebra. -/
  instCommRing : CommRing mid
  /-- The algebra structure over the common base ring. -/
  instAlgebra : Algebra R mid
  /-- The map from the left source into the common intermediate algebra. -/
  fromLeft : A →ₐ[R] mid
  /-- The map from the right source into the common intermediate algebra. -/
  fromRight : D →ₐ[R] mid
  /-- The map from the common intermediate algebra to the target. -/
  toTarget : mid →ₐ[R] B
  /-- The left triangle commutes. -/
  factorLeft : toTarget.comp fromLeft = fLeft
  /-- The right triangle commutes. -/
  factorRight : toTarget.comp fromRight = fRight

attribute [instance] CommonFactorisation.instCommRing
  CommonFactorisation.instAlgebra

namespace CommonFactorisation

variable {R : Type u} {A : Type v} {D : Type w} {B : Type x}
variable [CommRing R] [CommRing A] [CommRing D] [CommRing B]
variable [Algebra R A] [Algebra R D] [Algebra R B]
variable {fLeft : A →ₐ[R] B} {fRight : D →ₐ[R] B}

/-- The two triangle laws carried by a common factorisation. -/
theorem spec (F : CommonFactorisation fLeft fRight) :
    F.toTarget.comp F.fromLeft = fLeft ∧
      F.toTarget.comp F.fromRight = fRight := ⟨F.factorLeft, F.factorRight⟩

/-- Exchange the two sources of a common factorisation. -/
def swap (F : CommonFactorisation fLeft fRight) :
    CommonFactorisation fRight fLeft where
  mid := F.mid
  instCommRing := F.instCommRing
  instAlgebra := F.instAlgebra
  fromLeft := F.fromRight
  fromRight := F.fromLeft
  toTarget := F.toTarget
  factorLeft := F.factorRight
  factorRight := F.factorLeft

/-- Swapping a common factorisation exchanges its left source map. -/
@[simp]
theorem fromLeft_swap (F : CommonFactorisation fLeft fRight) :
    F.swap.fromLeft = F.fromRight := rfl

/-- Swapping a common factorisation exchanges its right source map. -/
@[simp]
theorem fromRight_swap (F : CommonFactorisation fLeft fRight) :
    F.swap.fromRight = F.fromLeft := rfl

/-- Swapping a common factorisation preserves its target map. -/
@[simp]
theorem toTarget_swap (F : CommonFactorisation fLeft fRight) :
    F.swap.toTarget = F.toTarget := rfl

/-- Exchanging the sources of a common factorisation twice is the identity. -/
@[simp]
theorem swap_swap (F : CommonFactorisation fLeft fRight) : F.swap.swap = F := rfl

/-- Build a common factorisation from its three algebra maps and two triangle
equations. -/
noncomputable def ofMaps
    {M : Type (max (max u v) (max w x))} [CommRing M] [Algebra R M]
    (fromLeft : A →ₐ[R] M) (fromRight : D →ₐ[R] M)
    (toTarget : M →ₐ[R] B)
    (factorLeft : toTarget.comp fromLeft = fLeft)
    (factorRight : toTarget.comp fromRight = fRight) :
    CommonFactorisation fLeft fRight :=
  { mid := M
    instCommRing := inferInstance
    instAlgebra := inferInstance
    fromLeft := fromLeft
    fromRight := fromRight
    toTarget := toTarget
    factorLeft := factorLeft
    factorRight := factorRight }

/-- The left source map of `CommonFactorisation.ofMaps` is the supplied map. -/
@[simp]
theorem fromLeft_ofMaps
    {M : Type (max (max u v) (max w x))} [CommRing M] [Algebra R M]
    (fromLeft : A →ₐ[R] M) (fromRight : D →ₐ[R] M)
    (toTarget : M →ₐ[R] B)
    (factorLeft : toTarget.comp fromLeft = fLeft)
    (factorRight : toTarget.comp fromRight = fRight) :
    (ofMaps fromLeft fromRight toTarget factorLeft factorRight).fromLeft =
      fromLeft := rfl

/-- The right source map of `CommonFactorisation.ofMaps` is the supplied map. -/
@[simp]
theorem fromRight_ofMaps
    {M : Type (max (max u v) (max w x))} [CommRing M] [Algebra R M]
    (fromLeft : A →ₐ[R] M) (fromRight : D →ₐ[R] M)
    (toTarget : M →ₐ[R] B)
    (factorLeft : toTarget.comp fromLeft = fLeft)
    (factorRight : toTarget.comp fromRight = fRight) :
    (ofMaps fromLeft fromRight toTarget factorLeft factorRight).fromRight =
      fromRight := rfl

/-- The target map of `CommonFactorisation.ofMaps` is the supplied map. -/
@[simp]
theorem toTarget_ofMaps
    {M : Type (max (max u v) (max w x))} [CommRing M] [Algebra R M]
    (fromLeft : A →ₐ[R] M) (fromRight : D →ₐ[R] M)
    (toTarget : M →ₐ[R] B)
    (factorLeft : toTarget.comp fromLeft = fLeft)
    (factorRight : toTarget.comp fromRight = fRight) :
    (ofMaps fromLeft fromRight toTarget factorLeft factorRight).toTarget =
      toTarget := rfl

/-- A common factorisation whose midpoint is finitely presented over the
base ring. -/
@[stacks 07CT "finite common factorisation of algebra maps"]
structure Finite (fLeft : A →ₐ[R] B) (fRight : D →ₐ[R] B) where
  /-- The underlying common factorisation. -/
  base : CommonFactorisation fLeft fRight
  /-- Finite presentation of the common midpoint, retained as an instance. -/
  [finitePresentation : Algebra.FinitePresentation R base.mid]

attribute [instance] Finite.finitePresentation

namespace Finite

/-- The midpoint of a finite-presentation common factorisation. -/
abbrev mid (F : Finite fLeft fRight) := F.base.mid

/-- The left source map of a finite-presentation common factorisation. -/
abbrev fromLeft (F : Finite fLeft fRight) : A →ₐ[R] F.mid :=
  F.base.fromLeft

/-- The right source map of a finite-presentation common factorisation. -/
abbrev fromRight (F : Finite fLeft fRight) : D →ₐ[R] F.mid :=
  F.base.fromRight

/-- The target map of a finite-presentation common factorisation. -/
abbrev toTarget (F : Finite fLeft fRight) : F.mid →ₐ[R] B :=
  F.base.toTarget

/-- The left triangle of a finite-presentation common factorisation. -/
theorem factorLeft (F : Finite fLeft fRight) :
    F.toTarget.comp F.fromLeft = fLeft := F.base.factorLeft

/-- The right triangle of a finite-presentation common factorisation. -/
theorem factorRight (F : Finite fLeft fRight) :
    F.toTarget.comp F.fromRight = fRight := F.base.factorRight

/-- The finite-presentation and triangle laws carried by a finite common
factorisation. -/
theorem spec (F : Finite fLeft fRight) :
    Algebra.FinitePresentation R F.mid ∧
      F.toTarget.comp F.fromLeft = fLeft ∧
      F.toTarget.comp F.fromRight = fRight := ⟨inferInstance, F.factorLeft, F.factorRight⟩

/-- Exchange the two sources of a finite common factorisation. -/
def swap (F : Finite fLeft fRight) : Finite fRight fLeft :=
  { base := F.base.swap
    finitePresentation := F.finitePresentation }

/-- Swapping a finite common factorisation exchanges its left source map. -/
@[simp]
theorem fromLeft_swap (F : Finite fLeft fRight) :
    F.swap.fromLeft = F.fromRight := rfl

/-- Swapping a finite common factorisation exchanges its right source map. -/
@[simp]
theorem fromRight_swap (F : Finite fLeft fRight) :
    F.swap.fromRight = F.fromLeft := rfl

/-- Swapping a finite common factorisation preserves its target map. -/
@[simp]
theorem toTarget_swap (F : Finite fLeft fRight) :
    F.swap.toTarget = F.toTarget := rfl

/-- Exchanging the sources of a finite common factorisation twice is the
identity. -/
@[simp]
theorem swap_swap (F : Finite fLeft fRight) : F.swap.swap = F := rfl

/-- Attach a finite-presentation instance to a common factorisation. -/
def of (F : CommonFactorisation fLeft fRight)
    [Algebra.FinitePresentation R F.mid] : Finite fLeft fRight :=
  { base := F }

/-- Build a finite-presentation common factorisation from three algebra maps. -/
noncomputable def ofMaps
    {M : Type (max (max u v) (max w x))} [CommRing M] [Algebra R M]
    [Algebra.FinitePresentation R M]
    (fromLeft : A →ₐ[R] M) (fromRight : D →ₐ[R] M)
    (toTarget : M →ₐ[R] B)
    (factorLeft : toTarget.comp fromLeft = fLeft)
    (factorRight : toTarget.comp fromRight = fRight) :
    Finite fLeft fRight :=
  { base := CommonFactorisation.ofMaps fromLeft fromRight toTarget
      factorLeft factorRight
    finitePresentation := inferInstanceAs (Algebra.FinitePresentation R M) }

/-- The left source map supplied to `Finite.ofMaps` is recovered by projection. -/
@[simp]
theorem fromLeft_ofMaps
    {M : Type (max (max u v) (max w x))} [CommRing M] [Algebra R M]
    [Algebra.FinitePresentation R M]
    (fromLeft : A →ₐ[R] M) (fromRight : D →ₐ[R] M)
    (toTarget : M →ₐ[R] B)
    (factorLeft : toTarget.comp fromLeft = fLeft)
    (factorRight : toTarget.comp fromRight = fRight) :
    (Finite.ofMaps fromLeft fromRight toTarget factorLeft factorRight).fromLeft =
      fromLeft := rfl

/-- The right source map supplied to `Finite.ofMaps` is recovered by projection. -/
@[simp]
theorem fromRight_ofMaps
    {M : Type (max (max u v) (max w x))} [CommRing M] [Algebra R M]
    [Algebra.FinitePresentation R M]
    (fromLeft : A →ₐ[R] M) (fromRight : D →ₐ[R] M)
    (toTarget : M →ₐ[R] B)
    (factorLeft : toTarget.comp fromLeft = fLeft)
    (factorRight : toTarget.comp fromRight = fRight) :
    (Finite.ofMaps fromLeft fromRight toTarget factorLeft factorRight).fromRight =
      fromRight := rfl

/-- The target map supplied to `Finite.ofMaps` is recovered by projection. -/
@[simp]
theorem toTarget_ofMaps
    {M : Type (max (max u v) (max w x))} [CommRing M] [Algebra R M]
    [Algebra.FinitePresentation R M]
    (fromLeft : A →ₐ[R] M) (fromRight : D →ₐ[R] M)
    (toTarget : M →ₐ[R] B)
    (factorLeft : toTarget.comp fromLeft = fLeft)
    (factorRight : toTarget.comp fromRight = fRight) :
    (Finite.ofMaps fromLeft fromRight toTarget factorLeft factorRight).toTarget =
      toTarget := rfl

end Finite

end CommonFactorisation

end AlgHom
