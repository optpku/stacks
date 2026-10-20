module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.TameBoundary
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.CategoryTheory.Conj

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.PreGaloisCategory
noncomputable section
universe u

namespace MultiplicativeGroupTame
variable (k : Type u) [Field k]

/-- Restrict the actual finite geometric fiber to the tame cover subcategory. -/
def fiber (η : GeometricPoint (space k)) : Cover k ⥤ FintypeCat.{u} :=
  inclusion k ⋙ η.finiteFiber

/-- Its usual topology is the subspace topology in the product of finite fiber automorphisms. -/
abbrev fundamentalGroup (η : GeometricPoint (space k)) : ProfiniteGrp.{u + 1} :=
  ProfiniteGrp.of (Aut (fiber k η))

def restrictionHom (η : GeometricPoint (space k)) : Aut η.finiteFiber →* Aut (fiber k η) :=
  ((whiskeringLeft _ _ FintypeCat).obj (inclusion k)).mapAut η.finiteFiber

theorem restriction_continuous (η : GeometricPoint (space k)) :
    Continuous (restrictionHom k η) := by
  sorry

/-- The canonical ordinary-to-tame homomorphism is restriction on components. -/
def quotientMap (η : GeometricPoint (space k)) :
    Aut η.finiteFiber →ₜ* fundamentalGroup k η :=
  ⟨restrictionHom k η, restriction_continuous k η⟩

theorem quotientMap_app (η : GeometricPoint (space k)) (σ : Aut η.finiteFiber) (V : Cover k) :
    (quotientMap k η σ).hom.app V = σ.hom.app V.obj := rfl

/-- Extension of compatible automorphisms along the tame Galois subcategory. -/
theorem quotient_surjective (η : GeometricPoint (space k)) :
    Function.Surjective (quotientMap k η) := by
  sorry

def constantPoint (η : GeometricPoint (space k)) : GeometricPoint (Spec (.of k)) :=
  η.map (structureMap k)

/-- The fixed pullback adjunction identifies the fibers of constant covers. -/
def constantFiberIso (η : GeometricPoint (space k)) :
    constants k ⋙ fiber k η ≅ (constantPoint k η).finiteFiber :=
  GeometricPoint.finiteFiberBaseChangeIso (structureMap k) η

/-- Degree before numerical normalization: restriction to actual constant covers. -/
def degreeHom (η : GeometricPoint (space k)) :
    fundamentalGroup k η →* Aut (constantPoint k η).finiteFiber :=
  (constantFiberIso k η).conjAut.toMonoidHom.comp
    (((whiskeringLeft _ _ FintypeCat).obj (constants k)).mapAut (fiber k η))

theorem degree_continuous (η : GeometricPoint (space k)) : Continuous (degreeHom k η) := by
  sorry

def degree (η : GeometricPoint (space k)) :
    fundamentalGroup k η →ₜ* Aut (constantPoint k η).finiteFiber :=
  ⟨degreeHom k η, degree_continuous k η⟩

theorem degree_app (η : GeometricPoint (space k)) (σ : fundamentalGroup k η)
    (V : Scheme.FiniteEtale (Spec (.of k))) :
    (degree k η σ).hom.app V =
      (constantFiberIso k η).inv.app V ≫ σ.hom.app ((constants k).obj V) ≫
        (constantFiberIso k η).hom.app V := rfl

/-- A rational point of the actual punctured line splits restriction to constants. -/
theorem degree_surjective (η : GeometricPoint (space k)) :
    Function.Surjective (degree k η) := by
  sorry

end MultiplicativeGroupTame
