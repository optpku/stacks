/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SmallBoundClosed.Operations
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped Cardinal AlgebraicGeometry

/- Lemma 3.9.9. Small bound-closed full subcategories of schemes have fibre products
and countable coproducts preserved by inclusion, and contain representatives of the
subschemes, bounded open gluings, and affine-ring constructions checked below. -/
@[stacks 000R] #check (AlgebraicGeometry.Scheme.isoClosure_pullback :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {X Y S : Scheme.{u}},
    P X →
    P Y →
    P S →
    ∀ (f : X ⟶ S) (g : Y ⟶ S),
    P.isoClosure (pullback f g))

#check (AlgebraicGeometry.Scheme.hasPullback :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {X Y S : P.FullSubcategory} (f : X ⟶ S) (g : Y ⟶ S),
    HasPullback f g)

#check (AlgebraicGeometry.Scheme.preservesPullback :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {X Y S : P.FullSubcategory} (f : X ⟶ S) (g : Y ⟶ S),
    PreservesLimit (cospan f g) P.ι)

#check (AlgebraicGeometry.Scheme.isoClosure_sigma :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {ι : Type u} [Countable ι] (S : ι → Scheme.{u}),
    (∀ i, P (S i)) →
    P.isoClosure (∐ S))

#check (AlgebraicGeometry.Scheme.hasCoproduct :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {ι : Type u} [Countable ι] (S : ι → P.FullSubcategory),
    HasCoproduct S)

#check (AlgebraicGeometry.Scheme.preservesCoproduct :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {ι : Type u} [Countable ι] (S : ι → P.FullSubcategory),
    PreservesColimit (Discrete.functor S) P.ι)

#check (AlgebraicGeometry.Scheme.isoClosure_of_isOpenImmersion :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {U S : Scheme.{u}},
    P S →
    ∀ (f : U ⟶ S) [IsOpenImmersion f],
    P.isoClosure U)

#check (AlgebraicGeometry.Scheme.isoClosure_of_isClosedImmersion :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {T S : Scheme.{u}},
    P S →
    ∀ (f : T ⟶ S) [IsClosedImmersion f],
    P.isoClosure T)

#check (AlgebraicGeometry.Scheme.isoClosure_of_finiteType :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {T S : Scheme.{u}},
    P S →
    ∀ (f : T ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f],
    P.isoClosure T)

#check (AlgebraicGeometry.Scheme.isoClosure_of_isOpenCover_size_le :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {S T : Scheme.{u}} {ι : Type u},
    P T →
    ∀ (U : ι → S.Opens),
    IsOpenCover U →
    (∀ i, (U i).toScheme.size ≤ T.size ^ ℵ₀) →
    #ι ≤ T.size ^ ℵ₀ →
    P.isoClosure S)

#check (AlgebraicGeometry.Scheme.isoClosure_of_locallyOfFiniteType_affine_le_power :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {T S : Scheme.{u}},
    P S →
    ∀ (f : T ⟶ S) [LocallyOfFiniteType f] {ι : Type u} (U : ι → T.Opens),
    IsOpenCover U →
    (∀ i, IsAffineOpen (U i)) →
    #ι ≤ S.size ^ ℵ₀ →
    P.isoClosure T)

#check (AlgebraicGeometry.Scheme.isoClosure_of_locallyOfFiniteType_affine_le_continuum :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {T S : Scheme.{u}},
    P S →
    ∀ (f : T ⟶ S) [LocallyOfFiniteType f] {ι : Type u} (U : ι → T.Opens),
    IsOpenCover U →
    (∀ i, IsAffineOpen (U i)) →
    #ι ≤ 2 ^ ℵ₀ →
    P.isoClosure T)

#check (AlgebraicGeometry.Scheme.isoClosure_of_mono :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {T S : Scheme.{u}},
    P S →
    ∀ (f : T ⟶ S) [Mono f],
    (QuasiCompact f ∨ LocallyOfFinitePresentation f) →
    P.isoClosure T)

#check (AlgebraicGeometry.Scheme.isoClosure_specAdicCompletion :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {T : Scheme.{u}},
    P T →
    ∀ [IsAffine T] (I : Ideal Γ(T, ⊤)),
    P.isoClosure (Spec (.of (AdicCompletion I Γ(T, ⊤)))))

#check (AlgebraicGeometry.Scheme.isoClosure_specFiniteType :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {T : Scheme.{u}},
    P T →
    ∀ [IsAffine T] {R' : Type u} [CommRing R'] [Algebra Γ(T, ⊤) R'] [Algebra.FiniteType Γ(T, ⊤) R'],
    P.isoClosure (Spec (.of R')))

#check (AlgebraicGeometry.Scheme.isoClosure_specLocalization :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {T : Scheme.{u}},
    P T →
    ∀ [IsAffine T] (S : Submonoid Γ(T, ⊤)),
    P.isoClosure (Spec (.of (Localization S))))

#check (AlgebraicGeometry.Scheme.isoClosure_specAlgebraicClosureResidueField :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {T : Scheme.{u}},
    P T →
    ∀ [IsAffine T] (p : Ideal Γ(T, ⊤)) [p.IsPrime],
    P.isoClosure (Spec (.of (AlgebraicClosure (Ideal.ResidueField p)))))

#check (AlgebraicGeometry.Scheme.isoClosure_specSubring :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {T : Scheme.{u}},
    P T →
    ∀ [IsAffine T] (R' : Subring Γ(T, ⊤)),
    P.isoClosure (Spec (.of R')))

#check (AlgebraicGeometry.Scheme.isoClosure_finiteTypeOverCardinal :
  ∀ {P : ObjectProperty Scheme.{u}},
    IsSmallBoundClosed P →
    ∀ {T : Scheme.{u}},
    P T →
    ∀ [IsAffine T] {A : Type u} [CommRing A],
    #A ≤ #(Γ(T, ⊤)) ^ ℵ₀ →
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f],
    P.isoClosure X)
