module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap75.Lemma_75_3_1_Restrict

/-!
# Lower shriek of modules along étale morphisms of algebraic spaces

For an étale morphism `j : U ⟶ X`, the functor `j_!` is extension by zero of `𝒪`-modules:
sheafification of the coproduct-indexed presheaf left adjoint of étale restriction. Because
étale `j_!` is exact, it induces a functor on unbounded derived categories by
`mapDerivedCategory`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits Opposite
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U X : AlgebraicSpace S}

/-- The morphism of algebraic spaces associated to an `S`-point of `Y`. -/
def homOfSchemePoint {T : Over S} {Y : AlgebraicSpace S}
    (p : Y.functorOfPoints.obj (op T)) : ofOver T ⟶ Y :=
  yonedaEquiv.symm p

/-- Factorizations of a scheme étale over `X` through an étale morphism `U ⟶ X`, as `S`-points
of `U` lying over the structure morphism. The index type is small, so the coproduct formula
for extension by zero is a coproduct in `ModuleCat.{u}`. -/
def lowerShriekIndex (f : U ⟶ X) [Etale f] (V : smallEtaleSite X) : Type u :=
  { p : U.functorOfPoints.obj (op V.left) // homOfSchemePoint p ≫ f = V.hom }

/-- The point of `U` underlying a factorization through `U ⟶ X`. -/
abbrev lowerShriekIndex.point (f : U ⟶ X) [Etale f] {V : smallEtaleSite X}
    (φ : lowerShriekIndex f V) : U.functorOfPoints.obj (op V.left) :=
  φ.val

/-- A factorization through `U ⟶ X` is étale by cancellation of étale morphisms. -/
instance etale_homOfSchemePoint_lowerShriekIndex (f : U ⟶ X) [Etale f] (V : smallEtaleSite X)
    (φ : lowerShriekIndex f V) : Etale (homOfSchemePoint (lowerShriekIndex.point f φ)) :=
  sorry

/-- The object of `U_étale` associated to a factorization of `V` through `U ⟶ X`. -/
def lowerShriekIndexSite (f : U ⟶ X) [Etale f] (V : smallEtaleSite X)
    (φ : lowerShriekIndex f V) : smallEtaleSite U :=
  smallEtaleSite.mk (homOfSchemePoint (lowerShriekIndex.point f φ))

/-- Pull a factorization of `W` through `U ⟶ X` back along a morphism `V ⟶ W` in `X_étale`. -/
def lowerShriekIndex.pull (f : U ⟶ X) [Etale f] {V W : smallEtaleSite X} (g : V ⟶ W)
    (φ : lowerShriekIndex f W) : lowerShriekIndex f V where
  val := U.functorOfPoints.map (op g.left) (lowerShriekIndex.point f φ)
  property := sorry

/-- The morphism in `U_étale` covering a morphism of `X_étale` on associated factorizations. -/
def lowerShriekIndexSite.map (f : U ⟶ X) [Etale f] {V W : smallEtaleSite X} (g : V ⟶ W)
    (φ : lowerShriekIndex f W) :
    lowerShriekIndexSite f V (lowerShriekIndex.pull f g φ) ⟶
      lowerShriekIndexSite f W φ :=
  MorphismProperty.CostructuredArrow.homMk g.left trivial sorry

/-- The comparison `j(V_φ) ⟶ V` in `X_étale` given by the identity on the underlying scheme. -/
def lowerShriekIndexToTarget (f : U ⟶ X) [Etale f] (V : smallEtaleSite X)
    (φ : lowerShriekIndex f V) :
    (restrictPostcompose f).obj (lowerShriekIndexSite f V φ) ⟶ V :=
  MorphismProperty.CostructuredArrow.homMk (𝟙 V.left) trivial sorry

/-- The comparison `V ⟶ j(V_φ)` in `X_étale` given by the identity on the underlying scheme. -/
def lowerShriekIndexToTargetInv (f : U ⟶ X) [Etale f] (V : smallEtaleSite X)
    (φ : lowerShriekIndex f V) :
    V ⟶ (restrictPostcompose f).obj (lowerShriekIndexSite f V φ) :=
  MorphismProperty.CostructuredArrow.homMk (𝟙 V.left) trivial sorry

/-- The factorization of `j(T)` through `U ⟶ X` associated to an object `T` of `U_étale`. -/
def indexOfSite (f : U ⟶ X) [Etale f] (T : smallEtaleSite U) :
    lowerShriekIndex f ((restrictPostcompose f).obj T) where
  val := yonedaEquiv (T.hom : ofOver T.left ⟶ U)
  property := by
    change homOfSchemePoint (yonedaEquiv T.hom) ≫ f = T.hom ≫ f
    rw [homOfSchemePoint, Equiv.symm_apply_apply]
    rfl

/-- The identity-on-left comparison from the factorization associated to `T` back to `T`. -/
def indexOfSiteIsoHom (f : U ⟶ X) [Etale f] (T : smallEtaleSite U) :
    lowerShriekIndexSite f ((restrictPostcompose f).obj T) (indexOfSite f T) ⟶ T :=
  MorphismProperty.CostructuredArrow.homMk (𝟙 T.left) trivial sorry

/-- The identity-on-left comparison `indexOfSiteIsoHom` induces the identity ring map. -/
theorem structureSheaf_map_indexOfSiteIsoHom (f : U ⟶ X) [Etale f] (T : smallEtaleSite U) :
    (structureSheaf U).obj.map (op (indexOfSiteIsoHom f T)) = 𝟙 _ := by
  have hscheme : (indexOfSiteIsoHom f T).left.left = 𝟙 T.left.left := rfl
  change (forget₂ CommRingCat RingCat).map
      (Scheme.Γ.map (indexOfSiteIsoHom f T).left.left.op) = 𝟙 _
  rw [hscheme]
  change (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (𝟙 (op T.left.left))) = 𝟙 _
  simp

/-- The identity-on-left comparison `lowerShriekIndexToTargetInv` induces the identity ring map. -/
theorem structureSheaf_map_lowerShriekIndexToTargetInv (f : U ⟶ X) [Etale f]
    (V : smallEtaleSite X) (φ : lowerShriekIndex f V) :
    (structureSheaf X).obj.map (op (lowerShriekIndexToTargetInv f V φ)) = 𝟙 _ := by
  have hscheme : (lowerShriekIndexToTargetInv f V φ).left.left = 𝟙 V.left.left := rfl
  change (forget₂ CommRingCat RingCat).map
      (Scheme.Γ.map (lowerShriekIndexToTargetInv f V φ).left.left.op) = 𝟙 _
  rw [hscheme]
  change (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (𝟙 (op V.left.left))) = 𝟙 _
  simp

/-- Restriction of functions along a morphism of `X_étale` agrees with restriction along the
associated morphism of `U_étale`. -/
theorem lowerShriekPresheaf_ringHom_eq (f : U ⟶ X) [Etale f]
    {V W : (smallEtaleSite X)ᵒᵖ} (α : V ⟶ W) (φ : lowerShriekIndex f V.unop) :
    ((structureSheaf U).obj.map (op (lowerShriekIndexSite.map f α.unop φ))).hom =
      ((structureSheaf X).obj.map α).hom := by
  have hleft :
      (lowerShriekIndexSite.map f α.unop φ).left.left = α.unop.left.left := rfl
  change RingCat.Hom.hom
      ((forget₂ CommRingCat RingCat).map
        (Scheme.Γ.map (lowerShriekIndexSite.map f α.unop φ).left.left.op)) =
    RingCat.Hom.hom
      ((forget₂ CommRingCat RingCat).map (Scheme.Γ.map α.unop.left.left.op))
  rw [hleft]
  rfl

/-- The coproduct summand of presheaf-level extension by zero indexed by a factorization
through `U ⟶ X`. -/
abbrev lowerShriekPresheafSummand (f : U ⟶ X) [Etale f]
    (M : PresheafOfModules.{u} (structureSheaf U).obj) (V : smallEtaleSite X)
    (φ : lowerShriekIndex f V) : ModuleCat.{u} ((structureSheaf X).obj.obj (op V)) :=
  M.obj (op (lowerShriekIndexSite f V φ))

/-- Objectwise extension by zero of a presheaf of modules, as the coproduct over factorizations
through `U ⟶ X`. -/
def lowerShriekPresheafObj (f : U ⟶ X) [Etale f]
    (M : PresheafOfModules.{u} (structureSheaf U).obj) (V : (smallEtaleSite X)ᵒᵖ) :
    ModuleCat.{u} ((structureSheaf X).obj.obj V) :=
  ∐ (lowerShriekPresheafSummand f M V.unop)

/-- Restriction maps of presheaf-level extension by zero. -/
def lowerShriekPresheafObjMap (f : U ⟶ X) [Etale f]
    (M : PresheafOfModules.{u} (structureSheaf U).obj) {V W : (smallEtaleSite X)ᵒᵖ}
    (α : V ⟶ W) :
    lowerShriekPresheafObj f M V ⟶
      (ModuleCat.restrictScalars ((structureSheaf X).obj.map α).hom).obj
        (lowerShriekPresheafObj f M W) :=
  Sigma.desc fun φ ↦
    M.map (op (lowerShriekIndexSite.map f α.unop φ)) ≫
      (ModuleCat.restrictScalarsCongr (lowerShriekPresheaf_ringHom_eq f α φ)).hom.app _ ≫
      (ModuleCat.restrictScalars ((structureSheaf X).obj.map α).hom).map
        (Sigma.ι (lowerShriekPresheafSummand f M W.unop)
          (lowerShriekIndex.pull f α.unop φ))

/-- Presheaf-level extension by zero along an étale morphism of algebraic spaces. -/
def lowerShriekPresheaf (f : U ⟶ X) [Etale f] :
    PresheafOfModules.{u} (structureSheaf U).obj ⥤
      PresheafOfModules.{u} (structureSheaf X).obj where
  obj M :=
    { obj := lowerShriekPresheafObj f M
      map := fun α ↦ lowerShriekPresheafObjMap f M α
      map_id := sorry
      map_comp := sorry }
  map {M N} α :=
    { app := fun V ↦
        Sigma.desc fun φ : lowerShriekIndex f V.unop ↦
          α.app (op (lowerShriekIndexSite f V.unop φ)) ≫
            Sigma.ι (lowerShriekPresheafSummand f N V.unop) φ
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- The forward map of the presheaf-level lower-shriek Hom equivalence, sending a morphism
out of extension by zero to a morphism into restriction. -/
def lowerShriekPresheafHomEquivToFun (f : U ⟶ X) [Etale f]
    {M : PresheafOfModules.{u} (structureSheaf U).obj}
    {N : PresheafOfModules.{u} (structureSheaf X).obj}
    (β : (lowerShriekPresheaf f).obj M ⟶ N) :
    M ⟶ (PresheafOfModules.pushforward.{u} (restrictStructureMap f).hom).obj N where
  app T :=
    M.map (op (indexOfSiteIsoHom f T.unop)) ≫
      (ModuleCat.restrictScalarsId'
          ((structureSheaf U).obj.map (op (indexOfSiteIsoHom f T.unop))).hom
          (congrArg RingCat.Hom.hom (structureSheaf_map_indexOfSiteIsoHom f T.unop))).hom.app _ ≫
      Sigma.ι (lowerShriekPresheafSummand f M ((restrictPostcompose f).obj T.unop))
        (indexOfSite f T.unop) ≫
      β.app (op ((restrictPostcompose f).obj T.unop))
  naturality := sorry

/-- The inverse map of the presheaf-level lower-shriek Hom equivalence, sending a morphism
into restriction to a morphism out of extension by zero. -/
def lowerShriekPresheafHomEquivInvFun (f : U ⟶ X) [Etale f]
    {M : PresheafOfModules.{u} (structureSheaf U).obj}
    {N : PresheafOfModules.{u} (structureSheaf X).obj}
    (α : M ⟶ (PresheafOfModules.pushforward.{u} (restrictStructureMap f).hom).obj N) :
    (lowerShriekPresheaf f).obj M ⟶ N where
  app V :=
    Sigma.desc fun φ : lowerShriekIndex f V.unop ↦
      α.app (op (lowerShriekIndexSite f V.unop φ)) ≫
        N.map (op (lowerShriekIndexToTargetInv f V.unop φ)) ≫
          (ModuleCat.restrictScalarsId'
              ((structureSheaf X).obj.map (op (lowerShriekIndexToTargetInv f V.unop φ))).hom
              (congrArg RingCat.Hom.hom
                (structureSheaf_map_lowerShriekIndexToTargetInv f V.unop φ))).hom.app _
  naturality := sorry

/-- The Hom equivalence exhibiting presheaf-level extension by zero as left adjoint to
presheaf-level pushforward along the identity-on-sections comparison. -/
def lowerShriekPresheafHomEquiv (f : U ⟶ X) [Etale f]
    (M : PresheafOfModules.{u} (structureSheaf U).obj)
    (N : PresheafOfModules.{u} (structureSheaf X).obj) :
    ((lowerShriekPresheaf f).obj M ⟶ N) ≃
      (M ⟶ (PresheafOfModules.pushforward.{u} (restrictStructureMap f).hom).obj N) where
  toFun := lowerShriekPresheafHomEquivToFun f
  invFun := lowerShriekPresheafHomEquivInvFun f
  left_inv := sorry
  right_inv := sorry

/-- Extension by zero `j_! : Mod(𝒪_U) ⥤ Mod(𝒪_X)` along an étale morphism of algebraic
spaces, obtained by sheafifying the coproduct formula for presheaf-level extension by zero. -/
def lowerShriek (f : U ⟶ X) [Etale f] : U.Modules ⥤ X.Modules :=
  forget (structureSheaf U) ⋙
    lowerShriekPresheaf f ⋙
      PresheafOfModules.sheafification.{u} (R₀ := (structureSheaf X).obj)
        (𝟙 (structureSheaf X).obj)

/-- The adjunction `j_! ⊣ j^*` for étale restriction of modules on algebraic spaces, assembled
from the coproduct Hom equivalence, sheafification, and fully faithful forgetful comparison. -/
def lowerShriekAdjunction (f : U ⟶ X) [Etale f] :
    lowerShriek f ⊣ restrictFunctor f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦
        ((PresheafOfModules.sheafificationAdjunction.{u}
            (𝟙 (structureSheaf X).obj)).homEquiv _ _).trans
          ((lowerShriekPresheafHomEquiv f M.val N.val).trans
            ((fullyFaithfulForget (structureSheaf U)).homEquiv
              (Y := (restrictFunctor f).obj N)).symm)
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- Lower shriek of modules along an étale morphism is additive. -/
instance lowerShriek_additive (f : U ⟶ X) [Etale f]
    [Abelian U.Modules] [Abelian X.Modules] :
    (lowerShriek f).Additive :=
  sorry

/-- Lower shriek of modules along an étale morphism preserves finite limits. -/
instance lowerShriek_preservesFiniteLimits (f : U ⟶ X) [Etale f]
    [Abelian U.Modules] [Abelian X.Modules] :
    PreservesFiniteLimits (lowerShriek f) :=
  sorry

/-- Lower shriek of modules along an étale morphism preserves finite colimits. -/
instance lowerShriek_preservesFiniteColimits (f : U ⟶ X) [Etale f]
    [Abelian U.Modules] [Abelian X.Modules] :
    PreservesFiniteColimits (lowerShriek f) :=
  sorry

/-- The derived étale lower-shriek functor `j_! : D(𝒪_U) ⥤ D(𝒪_X)`. -/
def lowerShriekDerived (f : U ⟶ X) [Etale f]
    [Abelian U.Modules] [Abelian X.Modules]
    [(lowerShriek f).Additive]
    [PreservesFiniteLimits (lowerShriek f)]
    [PreservesFiniteColimits (lowerShriek f)] :
    ModuleDerived U ⥤ ModuleDerived X :=
  @Functor.mapDerivedCategory U.Modules _ U.modulesAbelian (modulesHasDerivedCategory U)
    X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X) (lowerShriek f)
    inferInstance inferInstance inferInstance

/-- Derived étale lower shriek is `mapDerivedCategory` of underived étale lower shriek. -/
theorem lowerShriekDerived_eq (f : U ⟶ X) [Etale f]
    [Abelian U.Modules] [Abelian X.Modules]
    [(lowerShriek f).Additive]
    [PreservesFiniteLimits (lowerShriek f)]
    [PreservesFiniteColimits (lowerShriek f)] :
    lowerShriekDerived f =
      @Functor.mapDerivedCategory U.Modules _ U.modulesAbelian (modulesHasDerivedCategory U)
        X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X) (lowerShriek f)
        inferInstance inferInstance inferInstance :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
