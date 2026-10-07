module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Definition_87_23_2_Formal

/-!
# Adic* and locally adic* formal algebraic spaces

An affine formal algebraic space is adic* when it arises as the directed
colimit of `Spec (A ⧸ I ^ (n + 1))` for an adic ring `A` with a finitely
generated ideal of definition, with bonding maps the canonical power
quotients. A formal algebraic space is locally adic* when every étale
affine chart that is representable by algebraic spaces is adic*.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- An `ℕ`-indexed diagram of affine objects with thickening transitions has
sheaf colimit isomorphic to `X`. This is the `ℕ`-indexed form of
`IsDirectedAffineThickeningColimit`; that owner is indexed by
`Type (max u v)`, which does not unify with `ℕ`. -/
def IsNatDirectedAffineThickeningColimit {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  (∀ {i j : ℕ} (f : i ⟶ j),
      IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
    ∃ (c : Cocone
        (D ⋙ 𝒮.bigAffineInclusion S ⋙
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor)),
      Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt)

/-- The `ℕ`-indexed thickening colimit predicate unpacks as thickening
transitions together with a sheaf colimit isomorphic to `X`. -/
theorem isNatDirectedAffineThickeningColimit_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsNatDirectedAffineThickeningColimit D X ↔
      (∀ {i j : ℕ} (f : i ⟶ j),
          IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
        ∃ (c : Cocone
            (D ⋙ 𝒮.bigAffineInclusion S ⋙
              (𝒮.bigTopology S).sheafifiedRepresentableFunctor)),
          Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt) := sorry

/-- An `ℕ`-indexed diagram presents a sheaf as `Spf(A)` for an adic ring with a
finitely generated ideal of definition: it is a directed affine thickening
colimit, and the stage isomorphisms identify bonding maps with `Spec` of the
canonical quotients `A ⧸ I ^ (j + 1) →+* A ⧸ I ^ (i + 1)`. -/
def IsAdicPowerPresentation {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsAdicRing A]
    (I : Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))) : Prop :=
  I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I ∧
    IsNatDirectedAffineThickeningColimit D X ∧
      ∀ {i j : ℕ} (f : i ⟶ j),
        CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom (e j).hom
          (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.factorPow I (Nat.succ_le_succ (leOfHom f)))))

/-- An adic power presentation unpacks as a finitely generated topological
ideal of definition, an `ℕ`-indexed directed affine thickening colimit, and
commuting quotient squares on stages. -/
theorem isAdicPowerPresentation_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsAdicRing A]
    (I : Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))) :
    IsAdicPowerPresentation I D X e ↔
      I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I ∧
        IsNatDirectedAffineThickeningColimit D X ∧
          ∀ {i j : ℕ} (f : i ⟶ j),
            CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom (e j).hom
              (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.factorPow I
                  (Nat.succ_le_succ (leOfHom f))))) := sorry

/-- An adic power presentation is an `ℕ`-indexed directed affine thickening
colimit. -/
theorem IsAdicPowerPresentation.isNatDirectedAffineThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsAdicRing A]
    {I : Ideal A} {D : ℕ ⥤ 𝒮.bigAffineSite S}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))}
    (h : IsAdicPowerPresentation I D X e) :
    IsNatDirectedAffineThickeningColimit D X := sorry

/-- Stage bonding maps in an adic power presentation are `Spec` of the
canonical power quotients. -/
theorem IsAdicPowerPresentation.commSq {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsAdicRing A]
    {I : Ideal A} {D : ℕ ⥤ 𝒮.bigAffineSite S}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))}
    (h : IsAdicPowerPresentation I D X e) {i j : ℕ} (f : i ⟶ j) :
    CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom (e j).hom
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factorPow I (Nat.succ_le_succ (leOfHom f))))) :=
  sorry


/-- An affine formal algebraic space is adic* when it is the colimit of the
`ℕ`-indexed thickening system `Spec (A ⧸ I ^ (n + 1))` for an adic ring with a
finitely generated ideal of definition, with transition maps the canonical
power quotients. -/
class IsAdicStar {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsAffineFormalAlgebraicSpace X where
  /-- There is an adic presentation of `X` by successive quotients of a
  finitely generated ideal of definition, identified on objects and bonding
  maps. -/
  exists_adic_colimit :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicRing A)
      (I : Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
      (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
        Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))),
        IsAdicPowerPresentation I D X e

namespace IsAdicStar

/-- Exhibit an adic* affine formal algebraic space by an adic `ℕ`-indexed
presentation whose transitions are the canonical power quotients. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsAdicRing A]
    (I : Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I ^ (n + 1))))
    (h : IsAdicPowerPresentation I D X e) : IsAdicStar X := sorry

/-- An adic* affine formal algebraic space admits an adic `ℕ`-indexed
presentation by successive quotients, with bonding maps identified with
`Spec` of the canonical power quotients. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsAdicStar X] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicRing A)
      (I : Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
      (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
        Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))),
        IsAdicPowerPresentation I D X e := sorry

/-- An affine formal algebraic space is adic* iff it admits an adic `ℕ`-indexed
presentation by successive quotients with canonical bonding maps. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsAdicStar X ↔
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : IsAdicRing A) (I : Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
          (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
            Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))),
            IsAdicPowerPresentation I D X e := sorry

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is
adic*. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsAdicStar
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)) := sorry

end IsAdicStar

/-- A formal algebraic space is locally adic* when every morphism from an
affine formal algebraic space that is representable by algebraic spaces and
relatively étale has adic* source. -/
class IsLocallyAdicStar {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- Every representable étale morphism from an affine formal algebraic space
  has adic* source. -/
  of_etale_affine : ∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
    IsAffineFormalAlgebraicSpace Y →
      representableByAlgebraicSpaces f → relativelyEtale f → IsAdicStar Y

namespace IsLocallyAdicStar

/-- An adic* affine formal algebraic space is locally adic*. -/
instance ofAdicStar {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsAdicStar X] :
    IsLocallyAdicStar X := sorry

/-- Locally adic* unpacks as a formal algebraic space whose affine étale atlas
objects are adic*. -/
theorem iff_atlas {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsLocallyAdicStar X ↔
      IsFormalAlgebraicSpace X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, representableByAlgebraicSpaces (π i)) ∧
                (∀ i, relativelyEtale (π i)) ∧
                  Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                    ∀ i, IsAdicStar (X_ i) := sorry

/-- A locally adic* formal algebraic space has every representable étale affine
chart adic*. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsLocallyAdicStar X]
    {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace Y)
    (hrep : representableByAlgebraicSpaces f) (het : relativelyEtale f) :
    IsAdicStar Y := sorry

end IsLocallyAdicStar

end AlgebraicGeometry
