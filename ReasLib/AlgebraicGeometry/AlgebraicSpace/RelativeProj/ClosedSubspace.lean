/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.ClosedSubspace.Kernel

/-!
# Quotient presentations of closed subspaces of relative Proj

A closed subspace of `underline{Proj}_X(𝒜)` is presented as relative Proj of a
graded quotient `ℬ = 𝒜 / I` when the degreewise kernels of `𝒜 ⟶ ℬ` recover the
kernels of the canonical maps to `π_* ((i_* 𝒪_Z)(d))`, and the resulting
relative Proj is identified with `Z` as closed subspaces of `P`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable [𝒜.IsCommutative] [𝒜.IsQuasicoherent]
variable {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
variable (hF : F.IsAssociatedToQuadruples deg)
variable {Z : AlgebraicSpace S} (i : Z ⟶ toAlgebraicSpace F hF)
variable [IsClosedImmersion i]

/-- An identification with a closed subspace admits an étale-compatible quotient
functoriality map, and every such map has invertible domain inclusion and agrees
with the identification on the full source. -/
def IdentifiesClosedSubspace
    (algebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (algebra_isCommutative : algebra.IsCommutative)
    (algebra_isQuasicoherent : algebra.IsQuasicoherent)
    (quotientMap : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 algebra)
    {degB : DegreePieces algebra} (functor : ProjFunctor X algebra)
    (associated : functor.IsAssociatedToQuadruples degB)
    (iso : toAlgebraicSpace functor associated ≅ Z) : Prop :=
  let maps := @RelativeProjMap S X (toAlgebraicSpace F hF)
    (toAlgebraicSpace functor associated)
    (toAlgebraicSpace_hom F hF) (toAlgebraicSpace_hom functor associated)
    𝒜 algebra inferInstance algebra_isQuasicoherent
    (CanonicalTwists.family F hF).obj
    (CanonicalTwists.family functor associated).obj quotientMap
  let compatible := fun (r : maps) =>
    ∀ (W : Over S) (g : ofOver W ⟶ X) (hg : Etale g)
      (projA : AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg))
      (projB : AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)),
      Nonempty (@EtaleChartCompatibility S X 𝒜 algebra
        inferInstance algebra_isQuasicoherent
        deg degB F hF functor associated quotientMap r W g hg projA projB)
  (∃ r : maps, compatible r) ∧
    ∀ r : maps, compatible r →
      ∃ hFull : IsIso r.domain.ι,
        iso.hom ≫ i = mapOfFullDomain r hFull

/-- The functoriality map of an étale-compatible quotient homomorphism agrees with
`iso.hom ≫ i` on the full source. -/
theorem identifiesClosedSubspace_apply
    {algebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [algebra_isCommutative : algebra.IsCommutative]
    [algebra_isQuasicoherent : algebra.IsQuasicoherent]
    {quotientMap : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 algebra}
    {degB : DegreePieces algebra} {functor : ProjFunctor X algebra}
    {associated : functor.IsAssociatedToQuadruples degB}
    {iso : toAlgebraicSpace functor associated ≅ Z}
    (h : IdentifiesClosedSubspace F hF i algebra
      algebra_isCommutative algebra_isQuasicoherent quotientMap functor associated iso)
    (r : RelativeProjMap (toAlgebraicSpace_hom F hF)
      (toAlgebraicSpace_hom functor associated) 𝒜 algebra
      (CanonicalTwists.family F hF).obj
      (CanonicalTwists.family functor associated).obj quotientMap)
    (hcompat :
      ∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
      Nonempty (EtaleChartCompatibility hF associated r g)) :
    ∃ hFull : IsIso r.domain.ι,
      iso.hom ≫ i = mapOfFullDomain r hFull :=
  sorry

/-- A presentation of a closed subspace of relative Proj as
`underline{Proj}_X(ℬ)` for a graded quotient `𝒜 ⟶ ℬ`. -/
structure ClosedSubspaceQuotient where
  /-- The quotient graded algebra on `X`. -/
  algebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)
  /-- The quotient graded algebra is commutative. -/
  algebra_isCommutative : algebra.IsCommutative
  /-- Every degree of the quotient graded algebra is quasi-coherent. -/
  algebra_isQuasicoherent : algebra.IsQuasicoherent
  /-- The homomorphism from the original algebra to the quotient algebra. -/
  quotientMap : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 algebra
  /-- The quotient homomorphism is degreewise epic in nonnegative degrees. -/
  quotientMap_epi : ∀ d : ℕ, Epi (quotientMap.hom (Int.ofNat d))
  /-- Unlifted nonnegative degree pieces of the quotient algebra. -/
  degB : DegreePieces algebra
  /-- A relative projective functor of the quotient algebra. -/
  functor : ProjFunctor X algebra
  /-- The functor is associated to quadruples on `degB`. -/
  associated : functor.IsAssociatedToQuadruples degB
  /-- Identification of `underline{Proj}_X(ℬ)` with the closed subspace `Z`. -/
  iso : toAlgebraicSpace functor associated ≅ Z
  /-- The identification lies over `X`, with structure map `i ≫ π`. -/
  iso_over_X :
    iso.hom ≫ i ≫ toAlgebraicSpace_hom F hF =
      toAlgebraicSpace_hom functor associated
  /-- The identification agrees with every étale-compatible functoriality map of
  `quotientMap` as closed subspaces of `P`. -/
  identifiesClosedSubspace :
    IdentifiesClosedSubspace F hF i algebra
      algebra_isCommutative algebra_isQuasicoherent quotientMap functor associated iso

namespace ClosedSubspaceQuotient

/-- Construct a closed-subspace quotient presentation from its algebra, quotient map,
relative projective functor, identification over `X`, and closed-subspace comparison. -/
def ofComponents
    (algebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (algebra_isCommutative : algebra.IsCommutative)
    (algebra_isQuasicoherent : algebra.IsQuasicoherent)
    (quotientMap : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 algebra)
    (quotientMap_epi : ∀ d : ℕ, Epi (quotientMap.hom (Int.ofNat d)))
    (degB : DegreePieces algebra) (functor : ProjFunctor X algebra)
    (associated : functor.IsAssociatedToQuadruples degB)
    (iso : toAlgebraicSpace functor associated ≅ Z)
    (iso_over_X :
      iso.hom ≫ i ≫ toAlgebraicSpace_hom F hF =
        toAlgebraicSpace_hom functor associated)
    (identifiesClosedSubspace :
      IdentifiesClosedSubspace F hF i algebra
        algebra_isCommutative algebra_isQuasicoherent quotientMap functor associated iso) :
    ClosedSubspaceQuotient F hF i where
  algebra := algebra
  algebra_isCommutative := algebra_isCommutative
  algebra_isQuasicoherent := algebra_isQuasicoherent
  quotientMap := quotientMap
  quotientMap_epi := quotientMap_epi
  degB := degB
  functor := functor
  associated := associated
  iso := iso
  iso_over_X := iso_over_X
  identifiesClosedSubspace := identifiesClosedSubspace

/-- The defining commutativity, quasi-coherence, epimorphy, over-`X` identification,
and closed-subspace comparison of a closed-subspace quotient presentation. -/
theorem spec (Q : ClosedSubspaceQuotient F hF i) :
    Q.algebra.IsCommutative ∧ Q.algebra.IsQuasicoherent ∧
      (∀ d : ℕ, Epi (Q.quotientMap.hom (Int.ofNat d))) ∧
        (Q.iso.hom ≫ i ≫ toAlgebraicSpace_hom F hF =
          toAlgebraicSpace_hom Q.functor Q.associated) ∧
          IdentifiesClosedSubspace F hF i Q.algebra
            Q.algebra_isCommutative Q.algebra_isQuasicoherent Q.quotientMap Q.functor
            Q.associated Q.iso :=
  sorry

end ClosedSubspaceQuotient

/-- The unlifted nonnegative component of a quotient map, transported along the
degree-piece identifications of `𝒜` and `ℬ`. -/
def unliftedQuotientMap (Q : ClosedSubspaceQuotient F hF i) (d : ℕ) :
    deg.obj d ⟶ Q.degB.obj d :=
  Modules.unliftModuleHom
    ((deg.iso d).hom ≫ Q.quotientMap.hom (Int.ofNat d) ≫ (Q.degB.iso d).inv)

/-- Universe lift of `unliftedQuotientMap` recovers the degreewise quotient map. -/
theorem unliftedQuotientMap_spec (Q : ClosedSubspaceQuotient F hF i) (d : ℕ) :
    Modules.liftModuleMap (unliftedQuotientMap F hF i Q d) =
      (deg.iso d).hom ≫ Q.quotientMap.hom (Int.ofNat d) ≫ (Q.degB.iso d).inv :=
  sorry

/-- A canonical quotient presentation whose degreewise kernels are the kernels of the
maps to the pushed-forward restricted twists. -/
structure CanonicalClosedSubspaceQuotient extends ClosedSubspaceQuotient F hF i where
  /-- The kernel in every nonnegative degree is the canonical restricted-twist kernel. -/
  quotientMap_kernel : ∀ d : ℕ,
    kernelSubobject (unliftedQuotientMap F hF i toClosedSubspaceQuotient d) =
      closedSubspaceDegreeKernel F hF i d

namespace CanonicalClosedSubspaceQuotient

/-- Equip a quotient presentation with its degreewise canonical-kernel identification. -/
def ofQuotient (quotient : ClosedSubspaceQuotient F hF i)
    (quotientMap_kernel : ∀ d : ℕ,
      kernelSubobject (unliftedQuotientMap F hF i quotient d) =
        closedSubspaceDegreeKernel F hF i d) :
    CanonicalClosedSubspaceQuotient F hF i where
  toClosedSubspaceQuotient := quotient
  quotientMap_kernel := quotientMap_kernel

/-- The defining commutativity, quasi-coherence, epimorphy, over-`X` identification,
closed-subspace comparison, and canonical-kernel properties of a canonical
closed-subspace quotient presentation. -/
theorem spec (Q : CanonicalClosedSubspaceQuotient F hF i) :
    Q.algebra.IsCommutative ∧ Q.algebra.IsQuasicoherent ∧
      (∀ d : ℕ, Epi (Q.quotientMap.hom (Int.ofNat d))) ∧
        (Q.iso.hom ≫ i ≫ toAlgebraicSpace_hom F hF =
          toAlgebraicSpace_hom Q.functor Q.associated) ∧
          (IdentifiesClosedSubspace F hF i Q.algebra
            Q.algebra_isCommutative Q.algebra_isQuasicoherent Q.quotientMap Q.functor
            Q.associated Q.iso) ∧
            ∀ d : ℕ,
              kernelSubobject (unliftedQuotientMap F hF i Q.toClosedSubspaceQuotient d) =
                closedSubspaceDegreeKernel F hF i d :=
  sorry

end CanonicalClosedSubspaceQuotient

/-- Every closed subspace of a relative projective spectrum with quasi-compact
structure morphism is the relative projective spectrum of the graded quotient
by the canonical restricted-twist kernel. -/
theorem existsClosedSubspaceQuotient
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] [hqc : 𝒜.IsQuasicoherent]
    {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) {Z : AlgebraicSpace S}
    (i : Z ⟶ toAlgebraicSpace F hF)
    [IsClosedImmersion i] [QuasiCompact (toAlgebraicSpace_hom F hF)] :
    Nonempty (CanonicalClosedSubspaceQuotient F hF i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
