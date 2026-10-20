module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData

/-!
# Pullback of scheme descent data

A commutative square of scheme morphisms induces a functor between the corresponding
singleton-family categories of descent data. Different choices of the morphism across the
square give canonically naturally isomorphic functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DescentData.Pullback

variable {X X' S S' : Scheme.{u}}

/-- Pullback along a commutative square of scheme morphisms gives a functor on the associated
singleton-family categories of descent data. -/
noncomputable def functor (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S)
    (f : X' ⟶ X) (sq : CommSq f a' a h) :
    DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a) ⥤
      DescentData (fun _ : PUnit.{1} ↦ X') (fun _ : PUnit.{1} ↦ a') :=
  Pseudofunctor.DescentData.pullFunctor
    (p := h) (α := fun _ : PUnit.{1} ↦ PUnit.unit) (p' := fun _ ↦ f)
    Scheme.overPseudofunctor (fun _ ↦ sq.w)

/-- The object underlying the pulled descent datum is the pullback of the original object
along the top morphism of the square. -/
theorem functor_obj_obj (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S)
    (f : X' ⟶ X) (sq : CommSq f a' a h)
    (D : DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a)) :
    ((functor a a' h f sq).obj D).obj PUnit.unit =
      (Over.pullback f).obj (D.obj PUnit.unit) := sorry

/-- The transition map obtained by pseudofunctorially pulling back the original transition map
around a commutative square. -/
noncomputable def transitionMap (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S)
    (f : X' ⟶ X) (sq : CommSq f a' a h)
    (D : DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a))
    {Y : Scheme.{u}} (q : Y ⟶ S') (g₀ g₁ : Y ⟶ X')
    (hg₀ : g₀ ≫ a' = q) (hg₁ : g₁ ≫ a' = q) :
    (Scheme.overPseudofunctor.map g₀.op.toLoc).toFunctor.obj
        ((Scheme.overPseudofunctor.map f.op.toLoc).toFunctor.obj
          (D.obj PUnit.unit)) ⟶
      (Scheme.overPseudofunctor.map g₁.op.toLoc).toFunctor.obj
        ((Scheme.overPseudofunctor.map f.op.toLoc).toFunctor.obj
          (D.obj PUnit.unit)) :=
  Pseudofunctor.DescentData.pullFunctorObjHom
    (F := Scheme.overPseudofunctor) (f := fun _ : PUnit.{1} ↦ a)
    (p := h) (f' := fun _ : PUnit.{1} ↦ a')
    (α := fun _ : PUnit.{1} ↦ PUnit.unit) (p' := fun _ ↦ f)
    (j₁ := PUnit.unit) (j₂ := PUnit.unit)
    (fun _ : PUnit.{1} ↦ sq.w) D q g₀ g₁ hg₀ hg₁

/-- The transition map of the pulled datum is the canonical pullback transition map. -/
theorem functor_obj_hom (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S)
    (f : X' ⟶ X) (sq : CommSq f a' a h)
    (D : DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a))
    {Y : Scheme.{u}} (q : Y ⟶ S') (g₀ g₁ : Y ⟶ X')
    (hg₀ : g₀ ≫ a' = q) (hg₁ : g₁ ≫ a' = q) :
    ((functor a a' h f sq).obj D).hom
        (i₁ := PUnit.unit) (i₂ := PUnit.unit) q g₀ g₁ hg₀ hg₁ =
      transitionMap a a' h f sq D q g₀ g₁ hg₀ hg₁ := sorry

/-- Pullback maps a morphism of descent data by pulling back its unique component along the
top morphism of the square. -/
theorem functor_map_hom (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S)
    (f : X' ⟶ X) (sq : CommSq f a' a h)
    {D E : DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a)} (φ : D ⟶ E) :
    ((functor a a' h f sq).map φ).hom PUnit.unit =
      (Over.pullback f).map (φ.hom PUnit.unit) := sorry

/-- Two morphisms across the same commutative square boundary induce canonically naturally
isomorphic pullback functors on singleton-family descent data. -/
noncomputable def iso (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S)
    (f₀ f₁ : X' ⟶ X) (sq₀ : CommSq f₀ a' a h) (sq₁ : CommSq f₁ a' a h) :
    functor a a' h f₀ sq₀ ≅ functor a a' h f₁ sq₁ :=
  Pseudofunctor.DescentData.pullFunctorIso Scheme.overPseudofunctor
    (fun _ : PUnit.{1} ↦ sq₀.w) (fun _ : PUnit.{1} ↦ sq₁.w)

/-- The component of the canonical comparison is the descent-data isomorphism between the
two pullbacks of the original unique component. -/
theorem iso_hom_app_hom (a : X ⟶ S) (a' : X' ⟶ S') (h : S' ⟶ S)
    (f₀ f₁ : X' ⟶ X) (sq₀ : CommSq f₀ a' a h) (sq₁ : CommSq f₁ a' a h)
    (D : DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a)) :
    ((iso a a' h f₀ f₁ sq₀ sq₁).hom.app D).hom PUnit.unit =
      (D.iso (a' ≫ h) f₀ f₁ sq₀.w sq₁.w).hom := sorry

/-- Pullback by an endomorphism over the base is naturally isomorphic to the identity
functor on singleton-family descent data. -/
noncomputable def selfIso (a : X ⟶ S) (f : X ⟶ X) (sq : CommSq f a a (𝟙 S)) :
    functor a a (𝟙 S) f sq ≅
      𝟭 (DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a)) :=
  iso a a (𝟙 S) f (𝟙 X) sq CommSq.mk ≪≫
    Pseudofunctor.DescentData.pullFunctorIdIso Scheme.overPseudofunctor S

/-- The forward component of `selfIso` is the composite of the comparison with identity
pullback and the canonical identity-pullback component. -/
theorem selfIso_hom_app (a : X ⟶ S) (f : X ⟶ X) (sq : CommSq f a a (𝟙 S))
    (D : DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a)) :
    (selfIso a f sq).hom.app D =
      (iso a a (𝟙 S) f (𝟙 X) sq CommSq.mk).hom.app D ≫
        (Pseudofunctor.DescentData.pullFunctorIdIso
          Scheme.overPseudofunctor S).hom.app D := sorry

/-- Morphisms in both directions between schemes over a common base induce an equivalence
between their singleton-family categories of descent data. -/
noncomputable def equivalence (a : X ⟶ S) (a' : X' ⟶ S) (f : X' ⟶ X)
    (sqf : CommSq f a' a (𝟙 S)) (g : X ⟶ X') (sqg : CommSq g a a' (𝟙 S)) :
    DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a) ≌
      DescentData (fun _ : PUnit.{1} ↦ X') (fun _ : PUnit.{1} ↦ a') :=
  @Pseudofunctor.DescentData.pullFunctorEquivalence
    Scheme _ Scheme.overPseudofunctor PUnit.{1} S
    (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a) S PUnit.{1}
    (fun _ : PUnit.{1} ↦ X') (fun _ : PUnit.{1} ↦ a') (Iso.refl S)
    (fun _ : PUnit.{1} ↦ PUnit.unit) (fun _ : PUnit.{1} ↦ f) (fun _ ↦ sqf.w)
    (fun _ : PUnit.{1} ↦ PUnit.unit) (fun _ : PUnit.{1} ↦ g) (fun _ ↦ sqg.w)

/-- The forward functor of the descent-data equivalence is pullback along the morphism from
the second scheme to the first. -/
@[simp]
theorem equivalence_functor (a : X ⟶ S) (a' : X' ⟶ S) (f : X' ⟶ X)
    (sqf : CommSq f a' a (𝟙 S)) (g : X ⟶ X') (sqg : CommSq g a a' (𝟙 S)) :
    (equivalence a a' f sqf g sqg).functor = functor a a' (𝟙 S) f sqf := sorry

/-- The inverse functor of the descent-data equivalence is pullback along the morphism from
the first scheme to the second. -/
@[simp]
theorem equivalence_inverse (a : X ⟶ S) (a' : X' ⟶ S) (f : X' ⟶ X)
    (sqf : CommSq f a' a (𝟙 S)) (g : X ⟶ X') (sqg : CommSq g a a' (𝟙 S)) :
    (equivalence a a' f sqf g sqg).inverse = functor a' a (𝟙 S) g sqg := sorry

end AlgebraicGeometry.Scheme.DescentData.Pullback
