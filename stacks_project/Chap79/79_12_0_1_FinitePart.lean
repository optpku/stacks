module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap67.Lemma_67_45_5_Pullback

/-!
# Finite parts of morphisms of algebraic spaces

A pair `(a, Z)` for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, consisting of a morphism `a : T ⟶ Y` and an open subspace of the fibre
product `T ×_Y X` whose projection to `T` is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A pair `(a, Z)` consisting of a morphism `a : T ⟶ Y` over `S` and an open
subspace `Z` of `T ×_Y X` whose restricted projection `pr₀|_Z : Z ⟶ T` is finite. -/
structure FinitePart {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : AlgebraicSpace S) where
  /-- The morphism `a : T ⟶ Y` over `S`. -/
  a : T ⟶ Y
  /-- The open subspace `Z ⊂ T ×_Y X`. -/
  Z : OpenSubspace (pullback a f)
  /-- The restricted projection `Z.ι ≫ pullback.fst a f : Z.X ⟶ T` is finite. -/
  finite_pr : IsFinite (Z.ι ≫ pullback.fst a f)

namespace FinitePart

/-- Build a finite-part pair from a morphism `a : T ⟶ Y`, an open subspace of
`T ×_Y X`, and finiteness of the restricted first projection. -/
def of {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y} (a : T ⟶ Y)
    (Z : OpenSubspace (pullback a f)) (h : IsFinite (Z.ι ≫ pullback.fst a f)) :
    FinitePart f T where
  a := a
  Z := Z
  finite_pr := h

/-- Build a finite-part pair from a morphism `a : T ⟶ Y` and an open immersion
into `T ×_Y X` whose composite with `pr₀` is finite. -/
def ofι {S : Scheme.{u}} {X Y T W : AlgebraicSpace S} {f : X ⟶ Y} (a : T ⟶ Y)
    (ι : W ⟶ pullback a f) [IsOpenImmersion ι]
    (h : IsFinite (ι ≫ pullback.fst a f)) : FinitePart f T :=
  of a (OpenSubspace.ofι ι) h

/-- The restricted projection `pr₀|_Z : Z ⟶ T`. -/
def pr {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y}
    (p : FinitePart f T) : p.Z.X ⟶ T :=
  p.Z.ι ≫ pullback.fst p.a f

/-- The restricted projection is the open inclusion followed by `pr₀`. -/
theorem pr_eq {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y}
    (p : FinitePart f T) : p.pr = p.Z.ι ≫ pullback.fst p.a f :=
  sorry

/-- A finite-part pair consists of an open immersion into `T ×_Y X` whose
restricted first projection is finite. -/
theorem spec {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y}
    (p : FinitePart f T) : IsOpenImmersion p.Z.ι ∧ IsFinite p.pr :=
  sorry

/-- The type of finite-part pairs for a scheme `T` over `S`, recovered as an
algebraic space via `ofOver`. -/
abbrev over {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (T : Over S) :=
  FinitePart f (ofOver T)

/-- The maps `pr₀ ≫ h` and `pr₁` out of `T' ×_Y X` agree over `Y`, so they
induce `h × id_X : T' ×_Y X ⟶ T ×_Y X`. -/
theorem fiberMap_condition {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S}
    {f : X ⟶ Y} (p : FinitePart f T) (h : T' ⟶ T) :
    (pullback.fst (h ≫ p.a) f ≫ h) ≫ p.a = pullback.snd (h ≫ p.a) f ≫ f :=
  sorry

/-- The comparison `h × id_X : T' ×_Y X ⟶ T ×_Y X` induced by `h : T' ⟶ T`. -/
def fiberMap {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S} {f : X ⟶ Y}
    (p : FinitePart f T) (h : T' ⟶ T) :
    pullback (h ≫ p.a) f ⟶ pullback p.a f :=
  pullback.lift (pullback.fst (h ≫ p.a) f ≫ h) (pullback.snd (h ≫ p.a) f)
    (fiberMap_condition p h)

/-- The comparison `fiberMap p h` commutes with the first projections via `h`. -/
theorem fiberMap_fst {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S} {f : X ⟶ Y}
    (p : FinitePart f T) (h : T' ⟶ T) :
    fiberMap p h ≫ pullback.fst p.a f = pullback.fst (h ≫ p.a) f ≫ h :=
  sorry

/-- Base change of a pair `(a, Z)` along `h : T' ⟶ T`, sending `a` to `h ≫ a`
and `Z` to the inverse image `(h × id_X)⁻¹(Z)`. -/
def map {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S} {f : X ⟶ Y}
    (p : FinitePart f T) (h : T' ⟶ T) : FinitePart f T' where
  a := h ≫ p.a
  Z :=
    { X := pullback p.Z.ι (fiberMap p h)
      ι := pullback.snd p.Z.ι (fiberMap p h)
      isOpenImmersion :=
        IsOpenImmersion.pullback_snd p.Z.isOpenImmersion (fiberMap p h) }
  finite_pr := sorry

end FinitePart

end AlgebraicGeometry.AlgebraicSpace
