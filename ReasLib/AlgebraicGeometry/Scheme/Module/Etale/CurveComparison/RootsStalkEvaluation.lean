/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.RootsModuleSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LinearHomStalk
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.AssociatedModule
noncomputable section
universe u

namespace ActualRootsStalk
variable {Y : Scheme.{u}} [ConnectedSpace Y] (xbar : GeometricPoint Y) (n : ℕ)
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]

/-- Evaluate a lifted regular function at the specified geometric point of
the etale neighborhood, via global sections and the affine Spec counit. -/
def sectionRingMap (U : Y.Etale) (p : (geometricPointEtalePoint xbar).fiber.obj U) :
    (smallCommStructureSheaf .etale Y).obj.obj (op U) →+* xbar.K :=
  ((Scheme.ΓSpecIso (CommRingCat.of xbar.K)).hom.hom.comp
    (Scheme.Γ.map p.left.op).hom).comp ULift.ringEquiv.toRingHom

/-- A roots section is evaluated through the actual kernel inclusion and
the units of the same structure-ring section. -/
def sectionValue (U : Y.Etale) (p : (geometricPointEtalePoint xbar).fiber.obj U)
    (s : (ActualRootsModule.liftedSheaf Y n).obj.obj (op U)) :
    Additive (rootsOfUnity n xbar.K) :=
  Additive.ofMul ⟨Units.map (sectionRingMap xbar U p).toMonoidHom
    (Sheaf.unitsAddSheafUnit (smallCommStructureSheaf .etale Y)
      ((kernel.ι (Sheaf.unitsNsmul (smallCommStructureSheaf .etale Y) n)).hom.app (op U) s)), by sorry⟩

/-- A representative for an actual module stalk element. -/
structure Representative
    (s : (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} n) xbar).obj
      (ActualRootsModule.liftedSheaf Y n)) where
  U : Y.Etale
  point : (geometricPointEtalePoint xbar).fiber.obj U
  sectionValue : (ActualRootsModule.liftedSheaf Y n).obj.obj (op U)
  germ_eq : (geometricPointEtalePoint xbar).toPresheafFiber U point
    (ActualRootsModule.liftedSheaf Y n).obj sectionValue = s

theorem representative_nonempty
    (s : (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} n) xbar).obj
      (ActualRootsModule.liftedSheaf Y n)) : Nonempty (Representative xbar n s) := sorry

def evaluate
    (s : (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} n) xbar).obj
      (ActualRootsModule.liftedSheaf Y n)) : Additive (rootsOfUnity n xbar.K) :=
  let r := (representative_nonempty xbar n s).some
  sectionValue xbar n r.U r.point r.sectionValue

/-- Evaluation is unchanged when the germ is represented on a finer neighborhood. -/
theorem evaluate_germ (U : Y.Etale) (p : (geometricPointEtalePoint xbar).fiber.obj U)
    (s : (ActualRootsModule.liftedSheaf Y n).obj.obj (op U)) :
    evaluate xbar n ((geometricPointEtalePoint xbar).toPresheafFiber U p
      (ActualRootsModule.liftedSheaf Y n).obj s) = sectionValue xbar n U p s := sorry

def map : (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} n) xbar).obj
    (ActualRootsModule.liftedSheaf Y n) →+ Additive (rootsOfUnity n xbar.K) where
  toFun := evaluate xbar n
  map_zero' := sorry
  map_add' := sorry

/-- Smoothness of mu_n for n invertible ensures every residue-field root
lifts etale locally; the displayed evaluation map is then bijective. -/
theorem map_bijective (hn : IsUnit (n : xbar.K)) : Function.Bijective (map xbar n) := sorry

def equiv (hn : IsUnit (n : xbar.K)) :
    (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} n) xbar).obj
      (ActualRootsModule.liftedSheaf Y n) ≃+ Additive (rootsOfUnity n xbar.K) :=
  AddEquiv.ofBijective (map xbar n) (map_bijective xbar n hn)

end ActualRootsStalk
