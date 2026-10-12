/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_11_1_Formal

/-!
# Lemma 87.11.2

The diagonal of a formal algebraic space is representable, a monomorphism,
locally quasi-finite, locally of finite type, and separated, as a representable
transformation of fppf sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- Lemma 87.11.2 (1): Let `S` be a scheme. If `X` is a formal algebraic space
over `S`, then the diagonal morphism `Δ : X ⟶ X ×_S X` is representable. -/
@[stacks 0AIP]
theorem relativelyRepresentable_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) :=
  sorry

/-- Lemma 87.11.2 (2): Let `S` be a scheme. If `X` is a formal algebraic space
over `S`, then the diagonal morphism `Δ : X ⟶ X ×_S X` is a monomorphism. -/
@[stacks 0AIP]
theorem mono_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (MorphismProperty.inverseImage (MorphismProperty.monomorphisms Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) :=
  sorry

/-- Lemma 87.11.2 (3): Let `S` be a scheme. If `X` is a formal algebraic space
over `S`, then the diagonal morphism `Δ : X ⟶ X ×_S X` is locally
quasi-finite. -/
@[stacks 0AIP]
theorem locallyQuasiFinite_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (MorphismProperty.inverseImage (@LocallyQuasiFinite) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) :=
  sorry

/-- Lemma 87.11.2 (4): Let `S` be a scheme. If `X` is a formal algebraic space
over `S`, then the diagonal morphism `Δ : X ⟶ X ×_S X` is locally of finite
type. -/
@[stacks 0AIP]
theorem locallyOfFiniteType_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (MorphismProperty.inverseImage (@LocallyOfFiniteType) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) :=
  sorry

/-- Lemma 87.11.2 (5): Let `S` be a scheme. If `X` is a formal algebraic space
over `S`, then the diagonal morphism `Δ : X ⟶ X ×_S X` is separated. -/
@[stacks 0AIP]
theorem isSeparated_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (MorphismProperty.inverseImage (@IsSeparated) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) :=
  sorry

/-- Relative monomorphism of the diagonal unpacks as relative representability
together with monomorphisms of represented pullbacks on source schemes. -/
theorem mono_diag_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X ⨯ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) (diag X) ξ →
          Mono ((𝒮.bigToScheme S).map snd) :=
  sorry

/-- Relative local quasi-finiteness of the diagonal unpacks as relative
representability together with locally quasi-finite represented pullbacks on
source schemes. -/
theorem locallyQuasiFinite_diag_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X ⨯ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) (diag X) ξ →
          LocallyQuasiFinite ((𝒮.bigToScheme S).map snd) :=
  sorry

/-- Relative local finite type of the diagonal unpacks as relative
representability together with locally of finite type represented pullbacks on
source schemes. -/
theorem locallyOfFiniteType_diag_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X ⨯ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) (diag X) ξ →
          LocallyOfFiniteType ((𝒮.bigToScheme S).map snd) :=
  sorry

/-- Relative separatedness of the diagonal unpacks as relative representability
together with separated represented pullbacks on source schemes. -/
theorem isSeparated_diag_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X ⨯ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) (diag X) ξ →
          IsSeparated ((𝒮.bigToScheme S).map snd) :=
  sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
