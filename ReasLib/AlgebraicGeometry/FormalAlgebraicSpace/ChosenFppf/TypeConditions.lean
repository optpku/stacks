module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Topology.WeaklyAdmissible
public import ReasLib.RingTheory.Topology.Adic.Weakly
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicTypes
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.McQuillan

/-!
# Types of affine formal algebraic spaces on a chosen big fppf site

Noetherian, adic, weakly adic, classical, and countably indexed properties of
sheaves on a chosen big fppf site, together with their implication instances.
Adic, weakly adic, and classical presentations use a neighborhood basis of
(weak) ideals of definition. Presentation witnesses remain existential.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A directed affine thickening presentation of `X` by stages `Spec(A ⧸ (I λ))`
whose ideals `I λ` are ideals of definition forming a neighborhood basis of
`0`, hence `X` is `Spf(A)` rather than an arbitrary subdiagram, with bonding
maps identified with `Spec` of the canonical quotient maps along reverse
inclusion. -/
def IsIdealOfDefinitionPresentation {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (I : Λ → Ideal A) (D : Λ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
      Spec (CommRingCat.of (A ⧸ (I i)))) : Prop :=
  (∀ i, TopologicalRing.Ideal.IsIdealOfDefinition (I i)) ∧
    (∀ {i j : Λ}, i ≤ j → I j ≤ I i) ∧
      IsDirectedAffineThickeningColimit D X ∧
      (∀ {i j : Λ} (f : i ⟶ j) (hI : I j ≤ I i),
        CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom (e j).hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)))) ∧
      ∀ U ∈ nhds (0 : A), ∃ i, (I i : Set A) ⊆ U

/-- An ideal-of-definition presentation unpacks as ideals of definition,
reverse inclusion along morphisms, a directed affine thickening colimit,
commuting quotient squares on stages, and the family being a neighborhood
basis of `0`. -/
theorem isIdealOfDefinitionPresentation_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (I : Λ → Ideal A) (D : Λ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
      Spec (CommRingCat.of (A ⧸ (I i)))) :
    IsIdealOfDefinitionPresentation I D X e ↔
      (∀ i, TopologicalRing.Ideal.IsIdealOfDefinition (I i)) ∧
        (∀ {i j : Λ}, i ≤ j → I j ≤ I i) ∧
          IsDirectedAffineThickeningColimit D X ∧
          (∀ {i j : Λ} (f : i ⟶ j) (hI : I j ≤ I i),
            CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom (e j).hom
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)))) ∧
          ∀ U ∈ nhds (0 : A), ∃ i, (I i : Set A) ⊆ U :=
  sorry

/-- An ideal-of-definition presentation is a directed affine thickening
colimit. -/
theorem IsIdealOfDefinitionPresentation.isDirectedAffineThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    {I : Λ → Ideal A} {D : Λ ⥤ 𝒮.bigAffineSite S}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
      Spec (CommRingCat.of (A ⧸ (I i)))}
    (h : IsIdealOfDefinitionPresentation I D X e) :
    IsDirectedAffineThickeningColimit D X := sorry

/-- An ideal-of-definition presentation uses a neighborhood basis of `0`, so
the colimit is `Spf(A)` rather than an arbitrary subdiagram. -/
theorem IsIdealOfDefinitionPresentation.isNeighborhoodBasis
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    {I : Λ → Ideal A} {D : Λ ⥤ 𝒮.bigAffineSite S}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
      Spec (CommRingCat.of (A ⧸ (I i)))}
    (h : IsIdealOfDefinitionPresentation I D X e) :
    ∀ U ∈ nhds (0 : A), ∃ i, (I i : Set A) ⊆ U := sorry

/-- A directed affine thickening presentation of `X` by stages `Spec(A ⧸ (I λ))`
whose ideals `I λ` are weak ideals of definition forming a neighborhood basis
of `0`, hence `X` is `Spf(A)` rather than an arbitrary subdiagram, with bonding
maps identified with `Spec` of the canonical quotient maps along reverse
inclusion. -/
def IsWeakIdealOfDefinitionPresentation {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (I : Λ → Ideal A) (D : Λ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
      Spec (CommRingCat.of (A ⧸ (I i)))) : Prop :=
  (∀ i, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I i)) ∧
    (∀ {i j : Λ}, i ≤ j → I j ≤ I i) ∧
      IsDirectedAffineThickeningColimit D X ∧
      (∀ {i j : Λ} (f : i ⟶ j) (hI : I j ≤ I i),
        CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom (e j).hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)))) ∧
      ∀ U ∈ nhds (0 : A), ∃ i, (I i : Set A) ⊆ U

/-- A weak-ideal-of-definition presentation unpacks as weak ideals of
definition, reverse inclusion along morphisms, a directed affine thickening
colimit, commuting quotient squares on stages, and the family being a
neighborhood basis of `0`. -/
theorem isWeakIdealOfDefinitionPresentation_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (I : Λ → Ideal A) (D : Λ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
      Spec (CommRingCat.of (A ⧸ (I i)))) :
    IsWeakIdealOfDefinitionPresentation I D X e ↔
      (∀ i, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I i)) ∧
        (∀ {i j : Λ}, i ≤ j → I j ≤ I i) ∧
          IsDirectedAffineThickeningColimit D X ∧
          (∀ {i j : Λ} (f : i ⟶ j) (hI : I j ≤ I i),
            CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom (e j).hom
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)))) ∧
          ∀ U ∈ nhds (0 : A), ∃ i, (I i : Set A) ⊆ U :=
  sorry

/-- A weak-ideal-of-definition presentation is a directed affine thickening
colimit. -/
theorem IsWeakIdealOfDefinitionPresentation.isDirectedAffineThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    {I : Λ → Ideal A} {D : Λ ⥤ 𝒮.bigAffineSite S}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
      Spec (CommRingCat.of (A ⧸ (I i)))}
    (h : IsWeakIdealOfDefinitionPresentation I D X e) :
    IsDirectedAffineThickeningColimit D X := sorry

/-- A weak-ideal-of-definition presentation uses a neighborhood basis of `0`,
so the colimit is `Spf(A)` rather than an arbitrary subdiagram. -/
theorem IsWeakIdealOfDefinitionPresentation.isNeighborhoodBasis
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    {I : Λ → Ideal A} {D : Λ ⥤ 𝒮.bigAffineSite S}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
      Spec (CommRingCat.of (A ⧸ (I i)))}
    (h : IsWeakIdealOfDefinitionPresentation I D X e) :
    ∀ U ∈ nhds (0 : A), ∃ i, (I i : Set A) ⊆ U := sorry

/-- An affine formal algebraic space is Noetherian when it is McQuillan and
arises as the `ℕ`-indexed colimit of `Spec(A ⧸ I ^ (n + 1))` for an adic
Noetherian ring `A`. -/
class IsNoetherianAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsMcQuillan X where
  /-- There is an adic Noetherian presentation of `X` by successive quotients
  of an ideal of definition. -/
  exists_noetherian_adic_presentation :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicRing A)
      (_ : IsNoetherianRing A) (I : Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
      (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
        Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))),
        IsAdicPowerPresentation I D X e

namespace IsNoetherianAffine

/-- A sheaf satisfying the fixed-site presentation condition is a Noetherian
affine formal algebraic space if it has an adic Noetherian `ℕ`-indexed
presentation whose transitions are the canonical power quotients. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables X]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsAdicRing A]
    [IsNoetherianRing A] (I : Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I ^ (n + 1))))
    (h : IsAdicPowerPresentation I D X e) : IsNoetherianAffine X := sorry

/-- A Noetherian affine formal algebraic space admits an adic Noetherian
`ℕ`-indexed presentation by successive quotients. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsNoetherianAffine X] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicRing A)
      (_ : IsNoetherianRing A) (I : Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
      (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
        Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))),
        IsAdicPowerPresentation I D X e := sorry

/-- An affine formal algebraic space is Noetherian iff it is McQuillan and
admits an adic Noetherian `ℕ`-indexed presentation by successive quotients. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsNoetherianAffine X ↔
      IsMcQuillan X ∧
        ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : IsAdicRing A) (_ : IsNoetherianRing A) (I : Ideal A)
          (D : ℕ ⥤ 𝒮.bigAffineSite S)
          (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
            Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))),
            IsAdicPowerPresentation I D X e := sorry

/-- The sheafified representable of a Noetherian affine object of
`(Sch/S)_fppf` is a Noetherian affine formal algebraic space. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S)
    [IsNoetherian ((𝒮.bigAffineToScheme S).obj U)] :
    IsNoetherianAffine
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)) := sorry

end IsNoetherianAffine

/-- An affine formal algebraic space is adic when it is McQuillan and arises as
`Spf(A)` for an adic ring `A`: a directed colimit of `Spec(A ⧸ I)` along a
neighborhood basis of ideals of definition. -/
class IsAdicAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsMcQuillan X where
  /-- There is an adic presentation of `X` by `Spec(A ⧸ I)` as `I` runs over a
  neighborhood basis of ideals of definition, hence `X` is `Spf(A)`. -/
  exists_adic_presentation :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicRing A)
      (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (I : Λ → Ideal A) (D : Λ ⥤ 𝒮.bigAffineSite S)
      (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
        Spec (CommRingCat.of (A ⧸ (I i)))),
        IsIdealOfDefinitionPresentation I D X e

namespace IsAdicAffine

/-- A sheaf satisfying the fixed-site presentation condition is an adic
affine formal algebraic space if it has a directed presentation
`Spec(A ⧸ (I λ))` for a neighborhood basis of ideals of definition of an adic
ring, hence `X` is `Spf(A)`. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables X]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsAdicRing A]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (I : Λ → Ideal A) (D : Λ ⥤ 𝒮.bigAffineSite S)
    (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
      Spec (CommRingCat.of (A ⧸ (I i))))
    (h : IsIdealOfDefinitionPresentation I D X e) : IsAdicAffine X := sorry

/-- An adic affine formal algebraic space admits a directed presentation by
`Spec(A ⧸ I)` for a neighborhood basis of ideals of definition of an adic
ring, hence as `Spf(A)`. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsAdicAffine X] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicRing A)
      (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (I : Λ → Ideal A) (D : Λ ⥤ 𝒮.bigAffineSite S)
      (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
        Spec (CommRingCat.of (A ⧸ (I i)))),
        IsIdealOfDefinitionPresentation I D X e := sorry

/-- An affine formal algebraic space is adic iff it is McQuillan and admits a
directed presentation by `Spec(A ⧸ I)` for a neighborhood basis of ideals of
definition of an adic ring, hence as `Spf(A)`. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsAdicAffine X ↔
      IsMcQuillan X ∧
        ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : IsAdicRing A) (Λ : Type (max u v)) (_ : Preorder Λ)
          (_ : IsDirected Λ (· ≤ ·)) (I : Λ → Ideal A)
          (D : Λ ⥤ 𝒮.bigAffineSite S)
          (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
            Spec (CommRingCat.of (A ⧸ (I i)))),
            IsIdealOfDefinitionPresentation I D X e := sorry

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is
adic. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsAdicAffine
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)) := sorry

end IsAdicAffine

/-- An affine formal algebraic space is weakly adic when it is McQuillan and
arises as `Spf(A)` for a weakly adic ring `A`: a directed colimit of
`Spec(A ⧸ I)` along a neighborhood basis of weak ideals of definition. -/
class IsWeaklyAdicAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsMcQuillan X where
  /-- There is a weakly adic presentation of `X` by `Spec(A ⧸ I)` as `I` runs
  over a neighborhood basis of weak ideals of definition, hence `X` is
  `Spf(A)`. -/
  exists_weakly_adic_presentation :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsWeaklyAdicRing A) (Λ : Type (max u v)) (_ : Preorder Λ)
      (_ : IsDirected Λ (· ≤ ·)) (I : Λ → Ideal A)
      (D : Λ ⥤ 𝒮.bigAffineSite S)
      (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
        Spec (CommRingCat.of (A ⧸ (I i)))),
        IsWeakIdealOfDefinitionPresentation I D X e

namespace IsWeaklyAdicAffine

/-- A sheaf satisfying the fixed-site presentation condition is a weakly
adic affine formal algebraic space if it has a directed presentation
`Spec(A ⧸ (I λ))` for a neighborhood basis of weak ideals of definition of a
weakly adic ring, hence `X` is `Spf(A)`. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables X]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsWeaklyAdicRing A]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (I : Λ → Ideal A) (D : Λ ⥤ 𝒮.bigAffineSite S)
    (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
      Spec (CommRingCat.of (A ⧸ (I i))))
    (h : IsWeakIdealOfDefinitionPresentation I D X e) :
    IsWeaklyAdicAffine X := sorry

/-- A weakly adic affine formal algebraic space admits a directed presentation
by `Spec(A ⧸ I)` for a neighborhood basis of weak ideals of definition of a
weakly adic ring, hence as `Spf(A)`. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsWeaklyAdicAffine X] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsWeaklyAdicRing A) (Λ : Type (max u v)) (_ : Preorder Λ)
      (_ : IsDirected Λ (· ≤ ·)) (I : Λ → Ideal A)
      (D : Λ ⥤ 𝒮.bigAffineSite S)
      (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
        Spec (CommRingCat.of (A ⧸ (I i)))),
        IsWeakIdealOfDefinitionPresentation I D X e := sorry

/-- An affine formal algebraic space is weakly adic iff it is McQuillan and
admits a directed presentation by `Spec(A ⧸ I)` for a neighborhood basis of
weak ideals of definition of a weakly adic ring, hence as `Spf(A)`. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsWeaklyAdicAffine X ↔
      IsMcQuillan X ∧
        ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : IsWeaklyAdicRing A) (Λ : Type (max u v)) (_ : Preorder Λ)
          (_ : IsDirected Λ (· ≤ ·)) (I : Λ → Ideal A)
          (D : Λ ⥤ 𝒮.bigAffineSite S)
          (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
            Spec (CommRingCat.of (A ⧸ (I i)))),
            IsWeakIdealOfDefinitionPresentation I D X e := sorry

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is
weakly adic. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsWeaklyAdicAffine
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)) := sorry

end IsWeaklyAdicAffine

/-- An affine formal algebraic space is classical when it is McQuillan and
arises as `Spf(A)` for an admissible ring `A`: a directed colimit of
`Spec(A ⧸ I)` along a neighborhood basis of ideals of definition. -/
class IsClassicalAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsMcQuillan X where
  /-- There is a classical presentation of `X` by `Spec(A ⧸ I)` as `I` runs
  over a neighborhood basis of ideals of definition of an admissible ring,
  hence `X` is `Spf(A)`. -/
  exists_classical_presentation :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsAdmissibleRing A) (Λ : Type (max u v)) (_ : Preorder Λ)
      (_ : IsDirected Λ (· ≤ ·)) (I : Λ → Ideal A)
      (D : Λ ⥤ 𝒮.bigAffineSite S)
      (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
        Spec (CommRingCat.of (A ⧸ (I i)))),
        IsIdealOfDefinitionPresentation I D X e

namespace IsClassicalAffine

/-- A sheaf satisfying the fixed-site presentation condition is a classical
affine formal algebraic space if it has a directed presentation
`Spec(A ⧸ (I λ))` for a neighborhood basis of ideals of definition of an
admissible ring, hence `X` is `Spf(A)`. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables X]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsAdmissibleRing A]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (I : Λ → Ideal A) (D : Λ ⥤ 𝒮.bigAffineSite S)
    (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
      Spec (CommRingCat.of (A ⧸ (I i))))
    (h : IsIdealOfDefinitionPresentation I D X e) :
    IsClassicalAffine X := sorry

/-- A classical affine formal algebraic space admits a directed presentation by
`Spec(A ⧸ I)` for a neighborhood basis of ideals of definition of an
admissible ring, hence as `Spf(A)`. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsClassicalAffine X] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsAdmissibleRing A) (Λ : Type (max u v)) (_ : Preorder Λ)
      (_ : IsDirected Λ (· ≤ ·)) (I : Λ → Ideal A)
      (D : Λ ⥤ 𝒮.bigAffineSite S)
      (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
        Spec (CommRingCat.of (A ⧸ (I i)))),
        IsIdealOfDefinitionPresentation I D X e := sorry

/-- An affine formal algebraic space is classical iff it is McQuillan and
admits a directed presentation by `Spec(A ⧸ I)` for a neighborhood basis of
ideals of definition of an admissible ring, hence as `Spf(A)`. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsClassicalAffine X ↔
      IsMcQuillan X ∧
        ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : IsAdmissibleRing A) (Λ : Type (max u v)) (_ : Preorder Λ)
          (_ : IsDirected Λ (· ≤ ·)) (I : Λ → Ideal A)
          (D : Λ ⥤ 𝒮.bigAffineSite S)
          (e : ∀ i, ((𝒮.bigAffineToScheme S).obj (D.obj i)) ≅
            Spec (CommRingCat.of (A ⧸ (I i)))),
            IsIdealOfDefinitionPresentation I D X e := sorry

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is
classical. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsClassicalAffine
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)) := sorry

end IsClassicalAffine

/-- An affine formal algebraic space is countably indexed when it is a
sequential colimit of affine thickenings, equivalently a directed affine
thickening colimit whose index type is countable. -/
class IsCountablyIndexedAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsAffineFormalAlgebraicSpace X where
  /-- There is an `ℕ`-indexed directed affine thickening presentation of
  `X`. -/
  exists_nat_colimit :
    ∃ D : ℕ ⥤ 𝒮.bigAffineSite S, IsNatDirectedAffineThickeningColimit D X

namespace IsCountablyIndexedAffine

/-- Exhibit a countably indexed affine formal algebraic space by an
`ℕ`-indexed directed affine thickening colimit. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (h : IsNatDirectedAffineThickeningColimit D X) :
    IsCountablyIndexedAffine X := sorry

/-- A countably indexed affine formal algebraic space admits an `ℕ`-indexed
directed affine thickening presentation. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCountablyIndexedAffine X] :
    ∃ D : ℕ ⥤ 𝒮.bigAffineSite S, IsNatDirectedAffineThickeningColimit D X :=
  sorry

/-- An affine formal algebraic space is countably indexed iff it admits an
`ℕ`-indexed directed affine thickening presentation. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsCountablyIndexedAffine X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∃ D : ℕ ⥤ 𝒮.bigAffineSite S, IsNatDirectedAffineThickeningColimit D X :=
  sorry

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is
countably indexed, via the constant sequential system. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsCountablyIndexedAffine
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)) := sorry

end IsCountablyIndexedAffine

/-- A Noetherian affine formal algebraic space is adic*. -/
instance IsAdicStar.of_isNoetherianAffine {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsNoetherianAffine X] : IsAdicStar X := sorry

/-- An adic* affine formal algebraic space is adic. -/
instance IsAdicAffine.of_isAdicStar {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAdicStar X] : IsAdicAffine X := sorry

/-- An adic affine formal algebraic space is weakly adic. -/
instance IsWeaklyAdicAffine.of_isAdicAffine {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAdicAffine X] : IsWeaklyAdicAffine X := sorry

/-- A weakly adic affine formal algebraic space is classical. -/
instance IsClassicalAffine.of_isWeaklyAdicAffine {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsWeaklyAdicAffine X] : IsClassicalAffine X := sorry

/-- A weakly adic affine formal algebraic space is countably indexed. -/
instance IsCountablyIndexedAffine.of_isWeaklyAdicAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsWeaklyAdicAffine X] : IsCountablyIndexedAffine X := sorry

/-- A countably indexed affine formal algebraic space is McQuillan. -/
instance IsMcQuillan.of_isCountablyIndexedAffine {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCountablyIndexedAffine X] : IsMcQuillan X := sorry

end AlgebraicGeometry
