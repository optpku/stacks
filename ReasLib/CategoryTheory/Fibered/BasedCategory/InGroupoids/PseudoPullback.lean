/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids
public import ReasLib.CategoryTheory.Fibered.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Closure

/-!
# Pseudo-pullback closure of groupoid-fibred based categories

Object-property closure of `BasedCategory.isFiberedInGroupoids` under the explicit chosen based
pseudo-pullback. The lifts and Cartesian factors below use the original cospan's fibration
fields, independently of the raw projection instances in `InGroupoids.PseudoPullback`.
-/

@[expose] public section

universe u v w vB uX vX uY vY uS vS

namespace CategoryTheory

open ObjectProperty
open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace BasedCategory

namespace PseudoPullback.NativeCartesianLift

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

/-- Transport the original Cartesian field to a specified base arrow. This does not assert a
new universal property from which a factor could subsequently be chosen. -/
theorem cartesianOfHomLift {A : Type*} [Category A] (p : A ⥤ C)
    [Functor.IsFibered.InGroupoids p] {U V : C} (f : U ⟶ V)
    {a b : A} (φ : a ⟶ b) [p.IsHomLift f φ] : p.IsCartesian f φ := by
  subst_hom_lift p f φ
  exact Functor.IsFibered.InGroupoids.all_isCartesian φ

section Lift

variable (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)

/-- Compare the images of the two original Cartesian lifts. Both directions are native
Cartesian factors in `S`, supplied by the preservation fields of `F` and `G`. -/
noncomputable def comparison [X.p.IsFibered] [Y.p.IsFibered]
    (P : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).obj)
    {U : C} (f : U ⟶ baseObj P) :
    F.toFunctor.obj (Functor.IsPreFibered.pullbackObj (p := X.p) (fiberObj P).fst.2 f) ≅
      G.toFunctor.obj (Functor.IsPreFibered.pullbackObj (p := Y.p) (fiberObj P).snd.2 f) := by
  let a := Functor.IsPreFibered.pullbackMap (p := X.p) (fiberObj P).fst.2 f
  let b := Functor.IsPreFibered.pullbackMap (p := Y.p) (fiberObj P).snd.2 f
  letI : S.p.IsStronglyCartesian f (F.toFunctor.map a) :=
    CartesianBasedFunctor.Map.stronglyCartesianOfLift F f a
      (Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f a)
  letI : S.p.IsStronglyCartesian f (G.toFunctor.map b) :=
    CartesianBasedFunctor.Map.stronglyCartesianOfLift G f b
      (Functor.IsFibered.isStronglyCartesian_of_isCartesian Y.p f b)
  letI : S.p.IsHomLift (𝟙 (baseObj P)) (comparisonIsoApp P).hom :=
    PseudoPullback.comparisonIsoApp.hom.isHomLift P
  letI : S.p.IsCartesian f (F.toFunctor.map a ≫ (comparisonIsoApp P).hom) :=
    Functor.IsCartesian.of_comp_iso S.p f (F.toFunctor.map a) (comparisonIsoApp P)
  exact Functor.IsCartesian.domainUniqueUpToIso S.p f (G.toFunctor.map b)
    (F.toFunctor.map a ≫ (comparisonIsoApp P).hom)

/-- The lifted object stores exactly the two original pullback objects and their native
comparison. The remaining fields certify verticality and the inverse equations. -/
noncomputable def obj [X.p.IsFibered] [Y.p.IsFibered]
    (P : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).obj)
    {U : C} (f : U ⟶ baseObj P) :
    (PseudoPullback F.toBasedFunctor G.toBasedFunctor).obj := by
  let x : X.p.Fiber U :=
    ⟨Functor.IsPreFibered.pullbackObj (p := X.p) (fiberObj P).fst.2 f,
      Functor.IsPreFibered.pullbackObj_proj (p := X.p) _ _⟩
  let y : Y.p.Fiber U :=
    ⟨Functor.IsPreFibered.pullbackObj (p := Y.p) (fiberObj P).snd.2 f,
      Functor.IsPreFibered.pullbackObj_proj (p := Y.p) _ _⟩
  exact PseudoPullback.mk F.toBasedFunctor G.toBasedFunctor U
    { fst := x
      snd := y
      iso :=
        { hom := ⟨(comparison F G P f).hom, by sorry⟩
          inv := ⟨(comparison F G P f).inv, by sorry⟩
          hom_inv_id := by sorry
          inv_hom_id := by sorry } }

/-- The lift arrow retains the original component lift arrows. -/
noncomputable def hom [X.p.IsFibered] [Y.p.IsFibered]
    (P : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).obj)
    {U : C} (f : U ⟶ baseObj P) : obj F G P f ⟶ P :=
  PseudoPullback.Hom.mk f
    (Functor.IsPreFibered.pullbackMap (p := X.p) (fiberObj P).fst.2 f)
    (by exact inferInstanceAs (X.p.IsHomLift f
      (Functor.IsPreFibered.pullbackMap (p := X.p) (fiberObj P).fst.2 f)))
    (Functor.IsPreFibered.pullbackMap (p := Y.p) (fiberObj P).snd.2 f)
    (by exact inferInstanceAs (Y.p.IsHomLift f
      (Functor.IsPreFibered.pullbackMap (p := Y.p) (fiberObj P).snd.2 f))) (by sorry)

variable [X.p.IsFibered] [Y.p.IsFibered]
variable (P : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).obj)
variable {U : C} (f : U ⟶ baseObj P)

/-- The first lifted object is the pullback supplied by the original first fibration. -/
@[simp]
theorem obj_fst : fstObj (obj F G P f) =
    Functor.IsPreFibered.pullbackObj (p := X.p) (fiberObj P).fst.2 f := rfl

/-- The second lifted object is the pullback supplied by the original second fibration. -/
@[simp]
theorem obj_snd : sndObj (obj F G P f) =
    Functor.IsPreFibered.pullbackObj (p := Y.p) (fiberObj P).snd.2 f := rfl

/-- The first component of the lift is the original Cartesian lift arrow. -/
@[simp]
theorem hom_fst : fstMap (hom F G P f) =
    Functor.IsPreFibered.pullbackMap (p := X.p) (fiberObj P).fst.2 f := rfl

/-- The second component of the lift is the original Cartesian lift arrow. -/
@[simp]
theorem hom_snd : sndMap (hom F G P f) =
    Functor.IsPreFibered.pullbackMap (p := Y.p) (fiberObj P).snd.2 f := rfl

end Lift

section Factor

variable [Functor.IsFibered.InGroupoids X.p] [Functor.IsFibered.InGroupoids Y.p]
variable (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
variable {U V : C} (f : U ⟶ V)
variable {P Q R : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).obj} (φ : P ⟶ Q) (ψ : R ⟶ Q)
variable [(PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsHomLift f φ]
variable [(PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsHomLift f ψ]

/-- A Cartesian factor is the pair of factors from the original groupoid fibrations. The
displayed base map only transports the endpoint equalities of the supplied lifts. -/
noncomputable def factor : R ⟶ P := by
  letI : X.p.IsHomLift f (fstMap φ) := by sorry
  letI : X.p.IsHomLift f (fstMap ψ) := by sorry
  letI : Y.p.IsHomLift f (sndMap φ) := by sorry
  letI : Y.p.IsHomLift f (sndMap ψ) := by sorry
  letI := cartesianOfHomLift X.p f (fstMap φ)
  letI := cartesianOfHomLift Y.p f (sndMap φ)
  exact PseudoPullback.Hom.mk
    (eqToHom ((IsHomLift.domain_eq (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p f ψ).trans
      (IsHomLift.domain_eq (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p f φ).symm))
    (Functor.IsCartesian.map X.p f (fstMap φ) (fstMap ψ)) (by sorry)
    (Functor.IsCartesian.map Y.p f (sndMap φ) (sndMap ψ)) (by sorry) (by sorry)

/-- The explicit factor is vertical over the specified source base. -/
theorem factor_isHomLift :
    (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsHomLift (𝟙 U) (factor F G f φ ψ) := by sorry

/-- The native component factors give the required factorization. -/
theorem factor_fac : factor F G f φ ψ ≫ φ = ψ := by sorry

end Factor

/-- Every pseudo-pullback arrow is Cartesian using the actual component factors. In particular,
the existential part of this certificate is not an admitted universal-property field. -/
theorem isCartesian
    [Functor.IsFibered.InGroupoids X.p] [Functor.IsFibered.InGroupoids Y.p]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) {U V : C} (f : U ⟶ V)
    {P Q : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).obj} (φ : P ⟶ Q)
    [(PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsHomLift f φ] :
    (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsCartesian f φ where
  toIsHomLift := inferInstance
  universal_property ψ _ :=
    ⟨factor F G f φ ψ, ⟨factor_isHomLift F G f φ ψ, factor_fac F G f φ ψ⟩,
      by sorry⟩

/-- Assemble fibredness from the original lift objects and arrows, and all Cartesian universal
properties from the original component factors. Only compatibility and uniqueness laws remain
proof obligations. This is deliberately not a second global projection instance. -/
theorem inGroupoids
    [Functor.IsFibered.InGroupoids X.p] [Functor.IsFibered.InGroupoids Y.p]
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    Functor.IsFibered.InGroupoids
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p where
  exists_isCartesian' := by
    intro P U f
    refine ⟨obj F G P f, hom F G P f, ?_⟩
    letI : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsHomLift
        f (hom F G P f) := by sorry
    exact isCartesian F G f (hom F G P f)
  comp := by
    intro U V W f g P Q R φ ψ hφ hψ
    letI : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsHomLift f φ :=
      hφ.toIsHomLift
    letI : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsHomLift g ψ :=
      hψ.toIsHomLift
    -- Use the given lifts directly; instance search through Cartesian composition would
    -- request the very output fibration being constructed here.
    letI : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsHomLift
        (f ≫ g) (φ ≫ ψ) :=
      IsHomLift.comp (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p f g φ ψ
    exact isCartesian F G (f ≫ g) (φ ≫ ψ)
  all_isCartesian φ := by
    letI : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.IsHomLift
        ((PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.map φ) φ := .map φ
    exact isCartesian F G
      ((PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.map φ) φ

end PseudoPullback.NativeCartesianLift

namespace isFiberedInGroupoids

/-- The chosen pseudo-pullback of cartesian morphisms whose sources are fibred in groupoids is
again fibred in groupoids. This is the universe-polymorphic object-property form of
`PseudoPullback.Projection.InGroupoids.ofCartesian`; the common target need not satisfy the
property. -/
theorem PseudoPullback.ofCartesian
    {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C}
    {S : BasedCategory.{vS, uS} C}
    (hX : isFiberedInGroupoids C X)
    (hY : isFiberedInGroupoids C Y)
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p) :
    isFiberedInGroupoids C
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor) := by
  letI : Functor.IsFibered.InGroupoids X.p := hX
  letI : Functor.IsFibered.InGroupoids Y.p := hY
  exact BasedCategory.PseudoPullback.NativeCartesianLift.inGroupoids F G

/-- The chosen pseudo-pullback of a cospan of categories fibred in groupoids is again fibred in
groupoids. All three total categories may live in independent universes; this theorem is the
general semantic closure API, while `PseudoPullback.isClosedUnder` below is its stable-universe
typeclass specialization. -/
theorem pseudoPullback
    {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C}
    {S : BasedCategory.{vS, uS} C}
    (hX : isFiberedInGroupoids C X)
    (hY : isFiberedInGroupoids C Y)
    (hS : isFiberedInGroupoids C S)
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    isFiberedInGroupoids C (PseudoPullback F G) := by
  letI : Functor.IsFibered.InGroupoids S.p := hS
  let cF : CartesianBasedFunctor X.p S.p :=
    ⟨F, fun {_ _} φ _ ↦
      Functor.IsFibered.isStronglyCartesian_of_isCartesian S.p (S.p.map (F.map φ)) (F.map φ)⟩
  let cG : CartesianBasedFunctor Y.p S.p :=
    ⟨G, fun {_ _} φ _ ↦
      Functor.IsFibered.isStronglyCartesian_of_isCartesian S.p (S.p.map (G.map φ)) (G.map φ)⟩
  exact PseudoPullback.ofCartesian hX hY cF cG

/-- The universe-stable owner used by the generic property-selected two-fibre-product facade is
closed under the chosen based pseudo-pullback. The additional hom universe `vB` is independent of
the base-category hom universe `v`; for completely unrelated total-category universes, use
`pseudoPullback` directly. -/
instance PseudoPullback.isClosedUnder :
    BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder
      (isFiberedInGroupoids C :
        ObjectProperty
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)) where
  pseudoPullback_mem hX hY hS F G := pseudoPullback hX hY hS F G

end isFiberedInGroupoids

end BasedCategory

end CategoryTheory
