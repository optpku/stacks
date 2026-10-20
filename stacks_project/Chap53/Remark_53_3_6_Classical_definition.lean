/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LinearEquivalence
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LinearSystem
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LinearSubsystem
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LinearSeries

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/- Remark 53.3.6 (Classical definition) (1): two effective Cartier divisors are linearly
equivalent when their associated invertible modules are isomorphic. -/
@[stacks 0CCT] #check (AlgebraicGeometry.Scheme.IdealSheafData.linearlyEquivalent_def :
  ∀ (X : Scheme.{u}) (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι],
    linearlyEquivalent X D E ↔ Nonempty (D.associatedSheaf ≅ E.associatedSheaf))

/- Remark 53.3.6 (Classical definition) (2): on a smooth projective curve over an
algebraically closed field, linear equivalence is equality of the associated Picard classes. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.linearlyEquivalent_iff_picardClass_eq :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D E : X.left.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι],
    linearlyEquivalent X.left D E ↔
      Scheme.Modules.picardClass D.associatedSheaf =
        Scheme.Modules.picardClass E.associatedSheaf)

/- Remark 53.3.6 (Classical definition) (3): equivalently, two effective Cartier divisors
on the smooth projective curve are linearly equivalent exactly when their associated Picard
classes have the same image in the Weil divisor class group `Cl(X)`. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.linearlyEquivalent_iff_weilDivisorClass_eq :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D E : X.left.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι],
    let toCl := @Scheme.picardToWeilDivisorClassGroup X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom) inferInstance
    linearlyEquivalent X.left D E ↔
      toCl (Scheme.Modules.picardClass D.associatedSheaf) =
        toCl (Scheme.Modules.picardClass E.associatedSheaf))

/- Remark 53.3.6 (Classical definition) (4): the complete linear system of an effective
Cartier divisor `D` consists precisely of the effective Cartier divisors linearly equivalent
to `D`. -/
@[stacks 0CCT] #check (AlgebraicGeometry.Scheme.IdealSheafData.completeLinearSystem_def :
  ∀ (X : Scheme.{u}) (D E : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D.subschemeι],
    E ∈ completeLinearSystem X D ↔
      ∃ hE : IsEffectiveCartierDivisor E.subschemeι,
        @linearlyEquivalent X D E hD hE)

/- Remark 53.3.6 (Classical definition) (5): the natural scheme structure on `|D|` is the
scheme-theoretic fibre of the Abel map `γ_d` over the Picard point represented by `𝒪_X(D)`. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.CompleteLinearSystem.abelFibre_iso_scheme :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (d : ℕ)
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ)),
    Nonempty (CompleteLinearSystem.abelFibre X D d degree_eq ≅
      CompleteLinearSystem.scheme X D))

/- Remark 53.3.6 (Classical definition) (6): the effective divisors in `|D|` are exactly
the `k`-rational Hilbert points lying in the Abel-map fibre over `𝒪_X(D)`. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.CompleteLinearSystem.points_iff :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D E : X.left.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι] (d : ℕ)
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ)),
    E ∈ completeLinearSystem X.left D ↔
      ∃ p : (Over.mk (FieldExtension.specMap k k) : SchemeOverField k) ⟶
          CompleteLinearSystem.abelFibre X D d degree_eq,
        (Hilbert.rationalPointsEquiv X d
          (p ≫ pullback.fst (RelativePicard.abelMap X d)
            (CompleteLinearSystem.picardPoint X D d degree_eq))).ideal =
          E.comap (pullback.fst X.hom (FieldExtension.specMap k k)))

/- Remark 53.3.6 (Classical definition) (7): canonically, the complete-linear-system scheme
is `P(H⁰(X, 𝒪_X(D))ᵐᵒᵈᵘˡᵉ-ᵈᵘᵃˡ)`. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.CompleteLinearSystem.scheme_def :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι],
    CompleteLinearSystem.scheme X D =
      Over.mk (ProjectiveSpace.VectorSpace.toSpec k
        (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))))

/- Remark 53.3.6 (Classical definition) (8): if `m` is the dimension of `|D|`, then
`m + 1 = Module.finrank k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)`. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.CompleteLinearSystem.dimension_add_one :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (m : ℕ),
    topologicalKrullDim (CompleteLinearSystem.scheme X D).left = m →
      m + 1 = Module.finrank k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))

/- Remark 53.3.6 (Classical definition) (9): the complete-linear-system scheme is
isomorphic to projective `m`-space when the section-space dimension is `m + 1`. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.CompleteLinearSystem.scheme_iso_projectiveSpace :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (m : ℕ)
    (hdim : Module.finrank k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf) = m + 1),
    Nonempty (CompleteLinearSystem.scheme X D ≅
      Over.mk (ProjectiveSpace.toSpec k m)))

/- Remark 53.3.6 (Classical definition) (10): a subspace
`V ⊆ H⁰(X, 𝒪_X(D))` determines the projective linear subsystem `P(Vᵐᵒᵈᵘˡᵉ-ᵈᵘᵃˡ)`. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.LinearSubsystem.scheme_def :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)),
    LinearSubsystem.scheme X D V =
      Over.mk (ProjectiveSpace.VectorSpace.toSpec k (Module.Dual k V)))

/- Remark 53.3.6 (Classical definition) (11): the subspace `V` has a concrete inclusion into
`|D|`, obtained from its projective-model inclusion through the canonical isomorphism. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.LinearSubsystem.inclusion_left :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)),
    (LinearSubsystem.inclusion X D V).left =
      Proj.map (LinearSubsystem.gradedMap X D V)
        (LinearSubsystem.gradedMap_irrelevant X D V))

/- Remark 53.3.6 (Classical definition) (12): the projective subsystem determined by `V`
is a closed subvariety of the complete linear system `|D|`. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.LinearSubsystem.inclusion_isClosedImmersion :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)),
    IsClosedImmersion (LinearSubsystem.inclusion X D V).left)

/- Remark 53.3.6 (Classical definition) (13): the image of the subsystem determined by `V`
is cut out by the degree-one linear functionals vanishing on `V`. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.LinearSubsystem.gradedMap_ker :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)),
    RingHom.ker (LinearSubsystem.gradedMap X D V).toRingHom =
      LinearSubsystem.equationIdeal X D V)

/- Remark 53.3.6 (Classical definition) (14): in finite dimension, linear subsystems and
spaces of degree-one equations are equivalently described by section subspaces `V`. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.LinearSubsystem.equations_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    [FiniteDimensional k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))
    (equations : Submodule k
      (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))),
    LinearSubsystem.equations X D V = equations ↔
      V = LinearSubsystem.sectionSubspaceOfEquations X D equations)

/- Remark 53.3.6 (Classical definition) (15): a nonempty projective subsystem has geometric
dimension `r` exactly when its section subspace `V` has dimension `r + 1`. -/
@[stacks 0CCT] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.LinearSubsystem.dimension_eq_iff_finrank_eq :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))
    [FiniteDimensional k V] (hV : 0 < Module.finrank k V) (r : ℕ),
    topologicalKrullDim (LinearSubsystem.scheme X D V).left = r ↔
      Module.finrank k V = r + 1)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.LinearSeries

open Scheme Scheme.IdealSheafData

/- Remark 53.3.6 (Classical definition) (16): an effective Cartier divisor `D` of degree `d`
together with an `(r + 1)`-dimensional subspace `V ⊆ H⁰(X, 𝒪_X(D))` gives the corresponding
linear series `(𝒪_X(D), V)` of degree `d` and dimension `r`. -/
@[stacks 0CCT] #check (AlgebraicGeometry.LinearSeries.ofDivisorSubspace :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    {d r : ℕ}
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ))
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))
    [FiniteDimensional k V] (finrank_eq : Module.finrank k V = r + 1),
    LinearSeries X (topologicalKrullDim_eq_one X).le d r)

end AlgebraicGeometry.LinearSeries
