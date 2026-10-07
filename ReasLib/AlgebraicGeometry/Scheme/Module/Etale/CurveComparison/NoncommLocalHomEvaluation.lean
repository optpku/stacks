module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHom
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace NoncommLocalHomEvaluation
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
variable (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- Evaluation at the identity chart, with Hom first and the left-R section second. -/
def evaluation (U : Y.Etaleᵒᵖ)
    (α : NoncommLocalHom.Carrier h Y F J hc U) (m : F.obj.obj U) : J.obj.obj U :=
  (α.app (op (Over.mk (𝟙 U.unop)))).hom m

/-- The right action is actual precomposition, so the balancing equation is definitional. -/
theorem balanced (U : Y.Etaleᵒᵖ) (r : R)
    (α : NoncommLocalHom.Carrier h Y F J hc U) (m : F.obj.obj U) :
    evaluation h hc Y F J U (MulOpposite.op r • α) m =
      evaluation h hc Y F J U α (r • m) := rfl

/-- The native A-linear local-Hom action gives an actual A-bilinear evaluation. -/
def bilinear (U : Y.Etaleᵒᵖ) :
    NoncommLocalHom.Carrier h Y F J hc U →ₗ[A]
      (NoncommLocalHom.modules h).obj (F.obj.obj U) →ₗ[A] J.obj.obj U where
  toFun α := (α.app (op (Over.mk (𝟙 U.unop)))).hom
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Tensor only over the COMMUTATIVE coefficient ring A; R-balancing is separate. -/
def tensorEvaluation (U : Y.Etaleᵒᵖ) :
    TensorProduct A (NoncommLocalHom.Carrier h Y F J hc U)
      ((NoncommLocalHom.modules h).obj (F.obj.obj U)) →ₗ[A] J.obj.obj U :=
  TensorProduct.lift (bilinear h hc Y F J U)

/-- The tensor map agrees with actual identity-chart evaluation. -/
theorem tensorEvaluation_tmul (U : Y.Etaleᵒᵖ)
    (α : NoncommLocalHom.Carrier h Y F J hc U)
    (m : (NoncommLocalHom.modules h).obj (F.obj.obj U)) :
    tensorEvaluation h hc Y F J U (TensorProduct.tmul A α m) =
      evaluation h hc Y F J U α m := rfl

/-- Local evaluation commutes with restriction of both inputs to a smaller chart. -/
theorem naturality {U V : Y.Etaleᵒᵖ} (f : U ⟶ V)
    (α : NoncommLocalHom.Carrier h Y F J hc U) (m : F.obj.obj U) :
    (J.obj.map f).hom (evaluation h hc Y F J U α m) =
      evaluation h hc Y F J V
        (((NoncommLocalHom.obj h hc Y F J).obj.map f).hom α)
        ((F.obj.map f).hom m) := sorry

/-- Evaluation intertwines the actual contravariant/covariant local-Hom maps. -/
theorem map_evaluation
    {F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)}
    {J' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : F' ⟶ F) (g : J ⟶ J') (U : Y.Etaleᵒᵖ)
    (α : NoncommLocalHom.Carrier h Y F J hc U) (m : F'.obj.obj U) :
    evaluation h hc Y F' J' U
        (((NoncommLocalHom.map h hc Y f g).hom.app U).hom α) m =
      (g.hom.app U).hom (evaluation h hc Y F J U α ((f.hom.app U).hom m)) := rfl

end NoncommLocalHomEvaluation
