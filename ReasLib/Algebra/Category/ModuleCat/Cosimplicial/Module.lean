module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

@[expose] public section

open CategoryTheory Opposite PresheafOfModules

noncomputable section

universe u

/-- The commutative-ring diagram underlying a cosimplicial commutative ring. -/
abbrev cosimplicialCommRing (A : CosimplicialObject CommRingCat.{u}) :
    (SimplexCategoryᵒᵖ)ᵒᵖ ⥤ CommRingCat.{u} :=
  unopUnop SimplexCategory ⋙ A

/-- The ring diagram underlying a cosimplicial commutative ring. -/
abbrev moduleRingPresheaf (A : CosimplicialObject CommRingCat.{u}) :
    (SimplexCategoryᵒᵖ)ᵒᵖ ⥤ RingCat.{u} :=
  cosimplicialCommRing A ⋙ forget₂ CommRingCat RingCat

/-- Evaluation of the commutative-ring diagram is the original cosimplicial ring. -/
theorem cosimplicialCommRing_obj (A : CosimplicialObject CommRingCat.{u})
    (X : (SimplexCategoryᵒᵖ)ᵒᵖ) :
    (cosimplicialCommRing A).obj X = A.obj (unop (unop X)) :=
  rfl

/-- Evaluation of the module ring diagram is the underlying ring of the original diagram. -/
theorem moduleRingPresheaf_obj (A : CosimplicialObject CommRingCat.{u})
    (X : (SimplexCategoryᵒᵖ)ᵒᵖ) :
    (moduleRingPresheaf A).obj X =
      (forget₂ CommRingCat RingCat).obj (A.obj (unop (unop X))) :=
  rfl

variable {A : CosimplicialObject CommRingCat.{u}}

/-- The underlying additive cosimplicial object of a cosimplicial module. -/
abbrev underlyingAb (K : PresheafOfModules.{u} (moduleRingPresheaf A)) :
    CosimplicialObject Ab :=
  opOp SimplexCategory ⋙ K.presheaf

/-- The underlying additive morphism of a morphism of cosimplicial modules. -/
abbrev underlyingHom {K M : PresheafOfModules.{u} (moduleRingPresheaf A)}
    (φ : K ⟶ M) : underlyingAb K ⟶ underlyingAb M :=
  Functor.whiskerLeft (opOp SimplexCategory) ((toPresheaf (moduleRingPresheaf A)).map φ)

/-- The underlying additive object evaluates as the additive group of the module. -/
theorem underlyingAb_obj (K : PresheafOfModules.{u} (moduleRingPresheaf A))
    (n : SimplexCategory) :
    (underlyingAb K).obj n = K.presheaf.obj (op (op n)) :=
  rfl

/-- Components of the underlying morphism are the additive maps of the module morphism. -/
theorem underlyingHom_app {K M : PresheafOfModules.{u} (moduleRingPresheaf A)}
    (φ : K ⟶ M) (n : SimplexCategory) :
    (underlyingHom φ).app n = ((toPresheaf (moduleRingPresheaf A)).map φ).app (op (op n)) :=
  rfl
