module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LinearSheafHom
public import stacks_project.Chap59.Lemma_59_65_1_StalkRepresentation

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
noncomputable section
universe u

namespace ActualLinearHomStalk
variable {Y : Scheme.{u}} [ConnectedSpace Y]
variable (R : Type (u + 1)) [CommRing R] (xbar : GeometricPoint Y)
variable (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- A common pointed neighborhood representing the local morphism germ and
the input germ. The equalities fix exactly which elements are represented. -/
structure Representative
    (α : (StalkRepresentation.stalk R xbar).obj (ActualLinearSheafHom.obj Y R F G))
    (s : (StalkRepresentation.stalk R xbar).obj F) where
  U : Y.Etale
  point : (geometricPointEtalePoint xbar).fiber.obj U
  morphism : (ActualLinearSheafHom.obj Y R F G).obj.obj (op U)
  sectionValue : F.obj.obj (op U)
  morphism_germ : (geometricPointEtalePoint xbar).toPresheafFiber U point
    (ActualLinearSheafHom.obj Y R F G).obj morphism = α
  section_germ : (geometricPointEtalePoint xbar).toPresheafFiber U point F.obj sectionValue = s

/-- Filteredness gives a common representative for two germs. -/
theorem representative_nonempty
    (α : (StalkRepresentation.stalk R xbar).obj (ActualLinearSheafHom.obj Y R F G))
    (s : (StalkRepresentation.stalk R xbar).obj F) :
    Nonempty (Representative R xbar F G α s) := sorry

/-- Evaluate the local linear morphism before taking its germ. -/
def evaluateRepresentative
    {α : (StalkRepresentation.stalk R xbar).obj (ActualLinearSheafHom.obj Y R F G)}
    {s : (StalkRepresentation.stalk R xbar).obj F}
    (r : Representative R xbar F G α s) : (StalkRepresentation.stalk R xbar).obj G :=
  (geometricPointEtalePoint xbar).toPresheafFiber r.U r.point G.obj
    ((r.morphism.app (op (Over.mk (𝟙 r.U)))).hom r.sectionValue)

/-- Germ evaluation does not depend on the common representative. -/
theorem evaluateRepresentative_eq
    {α : (StalkRepresentation.stalk R xbar).obj (ActualLinearSheafHom.obj Y R F G)}
    {s : (StalkRepresentation.stalk R xbar).obj F}
    (r t : Representative R xbar F G α s) :
    evaluateRepresentative R xbar F G r = evaluateRepresentative R xbar F G t := sorry

/-- Quotient descent is implemented by representative evaluation with its
independence law, not by choosing a map between stalk objects. -/
def evaluate
    (α : (StalkRepresentation.stalk R xbar).obj (ActualLinearSheafHom.obj Y R F G))
    (s : (StalkRepresentation.stalk R xbar).obj F) : (StalkRepresentation.stalk R xbar).obj G :=
  evaluateRepresentative R xbar F G (representative_nonempty R xbar F G α s).some

/-- The explicit local evaluation is linear in both the morphism and its input. -/
def map : (StalkRepresentation.stalk R xbar).obj (ActualLinearSheafHom.obj Y R F G) →ₗ[R]
    ((StalkRepresentation.stalk R xbar).obj F →ₗ[R] (StalkRepresentation.stalk R xbar).obj G) where
  toFun α :=
    { toFun := evaluate R xbar F G α
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [hR : Finite R] [hF : Sheaf.IsFiniteTypeLocallyConstantModule F]

include hR hF in
/-- Local finite presentation makes the specified Hom/stalk map bijective.
Finite local constancy is essential; no assertion is made for arbitrary F. -/
theorem map_bijective : Function.Bijective (map R xbar F G) := sorry

def equiv : (StalkRepresentation.stalk R xbar).obj (ActualLinearSheafHom.obj Y R F G) ≃ₗ[R]
    ((StalkRepresentation.stalk R xbar).obj F →ₗ[R] (StalkRepresentation.stalk R xbar).obj G) :=
  LinearEquiv.ofBijective (map R xbar F G) (map_bijective R xbar F G)

end ActualLinearHomStalk
