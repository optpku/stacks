module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Spaces
public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Site

/-!
# Component inclusions of simplicial spaces

The inclusion of the open site at one degree into the diagram-open site of a
simplicial space, together with its associated sheaf functors and morphism of topoi.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

/-- The inclusion of the open site at degree `n` into the diagram-open site of a
simplicial space. -/
abbrev component (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    Opens (X.obj (op ⦋n⦌)) ⥤ DiagramOpens X :=
  DiagramOpens.fiber X (op ⦋n⦌)

/-- A component inclusion preserves pullbacks of opens. -/
instance instComponentPreservesLimitsOfShapeWalkingCospan
    (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    PreservesLimitsOfShape WalkingCospan (component X n) := sorry

/-- A component inclusion preserves equalizers of opens. -/
instance instComponentPreservesLimitsOfShapeWalkingParallelPair
    (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    PreservesLimitsOfShape WalkingParallelPair (component X n) := sorry

/-- A component inclusion is continuous from the ordinary open topology to the
diagram-open topology. -/
instance component_isContinuous (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    (component X n).IsContinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X) := sorry

/-- A component inclusion is cocontinuous from the ordinary open topology to the
diagram-open topology. -/
instance component_isCocontinuous (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    (component X n).IsCocontinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X) := sorry

/-- Inclusion at any simplex object is continuous for the open and diagram-open topologies. -/
instance fiber_isContinuous (Y : SimplicialObject TopCat.{u}) (c : SimplexCategoryᵒᵖ) :
    (DiagramOpens.fiber Y c).IsContinuous
      (Opens.grothendieckTopology (Y.obj c)) (zariskiTopology Y) := by
  change (component Y c.unop.len).IsContinuous
    (Opens.grothendieckTopology (Y.obj (op ⦋c.unop.len⦌))) (zariskiTopology Y)
  exact component_isContinuous Y c.unop.len

/-- Inclusion at any simplex object is cocontinuous for the open and diagram-open topologies. -/
instance fiber_isCocontinuous (Y : SimplicialObject TopCat.{u}) (c : SimplexCategoryᵒᵖ) :
    (DiagramOpens.fiber Y c).IsCocontinuous
      (Opens.grothendieckTopology (Y.obj c)) (zariskiTopology Y) := by
  change (component Y c.unop.len).IsCocontinuous
    (Opens.grothendieckTopology (Y.obj (op ⦋c.unop.len⦌))) (zariskiTopology Y)
  exact component_isCocontinuous Y c.unop.len

/-- Restriction `F ↦ F_c` of a diagram-open sheaf to the open site at a simplex object
`c`: the continuous direct image along `DiagramOpens.fiber Y c`. This is the canonical
owner of degree restriction; continuity is the global instance `fiber_isContinuous`. -/
abbrev sheafFiber (Y : SimplicialObject TopCat.{u}) (c : SimplexCategoryᵒᵖ)
    (A : Type (u + 1)) [Category.{u} A] :
    Sheaf (zariskiTopology Y) A ⥤ Sheaf (Opens.grothendieckTopology (Y.obj c)) A :=
  (DiagramOpens.fiber Y c).sheafPushforwardContinuous A
    (Opens.grothendieckTopology (Y.obj c)) (zariskiTopology Y)

/-- The morphism of topoi associated to a component inclusion. -/
noncomputable def componentMorphism (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [(component X n).IsCocontinuous
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)]
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u)]
    [∀ F : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasPointwiseRightKanExtension F] :
    MorphismOfTopoiIn (zariskiTopology X)
      (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) :=
  (component X n).morphismOfTopoiInOfCocontinuous
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)

/-- Restriction `F ↦ F_n` to the degree-`n` component, indexed by `n : ℕ` to match
`component`, `sheafLowerShriek` and `componentMorphism`. It is by definition
`sheafFiber X (op ⦋n⦌) A`. -/
abbrev sheafComponent (X : SimplicialObject TopCat.{u}) (n : ℕ)
    (A : Type (u + 1)) [Category.{u} A] :
    Sheaf (zariskiTopology X) A ⥤
      Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) A :=
  sheafFiber X (op ⦋n⦌) A

/-- The type-valued lower-shriek functor along a component inclusion. -/
noncomputable abbrev sheafLowerShriek (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasLeftKanExtension P] :
    Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u) ⥤
      Sheaf (zariskiTopology X) (Type u) :=
  (component X n).sheafPullback (Type u)
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)

/-- The abelian lower-shriek functor along a component inclusion. -/
noncomputable abbrev abelianLowerShriek (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasWeakSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ AddCommGrpCat.{u},
      (component X n).op.HasLeftKanExtension P] :
    Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) AddCommGrpCat.{u} ⥤
      Sheaf (zariskiTopology X) AddCommGrpCat.{u} :=
  (component X n).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)

/-- The inverse image of the component morphism of topoi is canonically isomorphic to
restriction along the component inclusion. -/
noncomputable def componentMorphism_inverseImage_iso_sheafComponent
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u)]
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [∀ F : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasPointwiseRightKanExtension F] :
    (componentMorphism X n)⁻¹ ≅ sheafComponent X n (Type u) :=
  let G := component X n
  let J := Opens.grothendieckTopology (X.obj (op ⦋n⦌))
  let K := zariskiTopology X
  (Functor.associator (sheafToPresheaf K (Type u))
      ((Functor.whiskeringLeft _ _ (Type u)).obj G.op) (presheafToSheaf J (Type u))) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf K (Type u))
      (G.pushforwardContinuousSheafificationCompatibility (Type u) J K) ≪≫
    (Functor.associator (sheafToPresheaf K (Type u)) (presheafToSheaf K (Type u))
      (G.sheafPushforwardContinuous (Type u) J K)).symm ≪≫
    Functor.isoWhiskerRight (sheafificationNatIso K (Type u)).symm
      (G.sheafPushforwardContinuous (Type u) J K) ≪≫
    Functor.leftUnitor (G.sheafPushforwardContinuous (Type u) J K)

/-- The forward component of the canonical inverse-image comparison agrees with the
sheafification-compatibility map followed by undoing sheafification of a sheaf. -/
theorem componentMorphism_inverseImage_iso_sheafComponent_hom_app
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u)]
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [∀ F : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasPointwiseRightKanExtension F]
    (F : Sheaf (zariskiTopology X) (Type u)) :
    (componentMorphism_inverseImage_iso_sheafComponent X n).hom.app F =
      Functor.CocontinuousPullback.comparisonApp (component X n)
        (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X) F := sorry

/-- The chosen type-valued lower shriek is left adjoint to restriction to a component. -/
noncomputable def sheafLowerShriek_adjunction
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasLeftKanExtension P] :
    sheafLowerShriek X n ⊣ sheafComponent X n (Type u) :=
  (component X n).sheafAdjunctionContinuous (Type u)
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)

/-- Restriction of type-valued sheaves along a component inclusion is a right adjoint. -/
instance sheafComponent_isRightAdjoint (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasLeftKanExtension P] :
    (sheafComponent X n (Type u)).IsRightAdjoint :=
  (sheafLowerShriek_adjunction X n).isRightAdjoint

/-- Type-valued lower shriek along a component inclusion preserves finite connected limits. -/
instance sheafLowerShriek_preservesFiniteConnectedLimits
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasSheafify (zariskiTopology X) (Type u)]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasPointwiseLeftKanExtension P] :
    PreservesFiniteConnectedLimits (sheafLowerShriek X n) :=
  Functor.SheafPullback.Pullbacks.ofEqualizers (component X n)

/-- The chosen abelian lower shriek is left adjoint to restriction to a component. -/
noncomputable def abelianLowerShriek_adjunction
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasWeakSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ AddCommGrpCat.{u},
      (component X n).op.HasLeftKanExtension P] :
    abelianLowerShriek X n ⊣ sheafComponent X n AddCommGrpCat.{u} :=
  (component X n).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (zariskiTopology X)

/-- Restriction of abelian sheaves along a component inclusion is a right adjoint. -/
instance abelianSheafComponent_isRightAdjoint
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasWeakSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ AddCommGrpCat.{u},
      (component X n).op.HasLeftKanExtension P] :
    (sheafComponent X n AddCommGrpCat.{u}).IsRightAdjoint :=
  (abelianLowerShriek_adjunction X n).isRightAdjoint

/-- Abelian lower shriek along a component inclusion is exact. -/
theorem abelianLowerShriek_exact (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [HasSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ AddCommGrpCat.{u},
      (component X n).op.HasPointwiseLeftKanExtension P] :
    exactFunctor
      (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) AddCommGrpCat.{u})
      (Sheaf (zariskiTopology X) AddCommGrpCat.{u})
      (abelianLowerShriek X n) :=
  Functor.AbelianLowerShriek.exact_of_preservesPullbacksAndEqualizers (component X n)

end CategoryTheory.SimplicialObject
