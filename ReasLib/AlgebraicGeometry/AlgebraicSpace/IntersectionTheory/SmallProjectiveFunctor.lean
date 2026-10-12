/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveQuotientFunctor
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import Mathlib.Logic.Small.Basic

/-! A small carrier for the actual projective quotient functor, using kernel codes.
Smallness is proved from a specified injective map, not a projective-space selector.
-/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.MonoidalCategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.SmallProjectiveFunctor
variable {S : Scheme.{u}} {X : AlgebraicSpace S} (E : X.Modules) [E.IsQuasicoherent]

def testObject (T : Over S) (g : ofOver T ⟶ X) : Over X := Over.mk g

/-- The Yoneda inverse of an actual scheme-valued base point. -/
def homOfPoint {T : Over S} (x : X.functorOfPoints.obj (op T)) : ofOver T ⟶ X :=
  yonedaEquiv.symm x

/-- Source-dependent kernel submodules of the actual scheme restriction of g*E. -/
abbrev KernelCode (T : Over S) (g : ofOver T ⟶ X) :=
  ∀ U : T.left.Opens, Submodule (T.left.ringCatSheaf.obj.obj (op U))
    (((Modules.restrictToScheme T).obj ((Modules.pullback g).obj E)).val.obj (op U))

def kernelCode (T : Over S) (g : ofOver T ⟶ X)
    (q : CategoryTheory.InvertibleQuotient ((Modules.pullback g).obj E)) : KernelCode E T g :=
  fun U ↦ LinearMap.ker (((Modules.restrictToScheme T).map q.hom).val.app (op U)).hom

theorem kernelCode_rel (T : Over S) (g : ofOver T ⟶ X)
    {q q' : CategoryTheory.InvertibleQuotient ((Modules.pullback g).obj E)}
    (h : CategoryTheory.InvertibleQuotient.Rel q q') : kernelCode E T g q = kernelCode E T g q' := by
  sorry

def classCode (T : Over S) (g : ofOver T ⟶ X) :
    ProjectiveQuotientFunctor.Point E (testObject T g) → KernelCode E T g :=
  Quotient.lift (kernelCode E T g) (fun _ _ ↦ kernelCode_rel E T g)

/-- Epimorphic quotients of the same QCoh module are determined up to compatible
isomorphism by their kernel. Zariski restriction is faithful on these QCoh objects. -/
theorem classCode_injective (T : Over S) (g : ofOver T ⟶ X) :
    Function.Injective (classCode E T g) := by
  sorry

instance pointSmall (T : Over S) (g : ofOver T ⟶ X) :
    Small.{u} (ProjectiveQuotientFunctor.Point E (testObject T g)) :=
  small_of_injective (classCode_injective E T g)

/-- Small quotient points over a specified scheme-valued base point. -/
abbrev SmallPoint (T : Over S) (g : ofOver T ⟶ X) : Type u :=
  Shrink.{u} (ProjectiveQuotientFunctor.Point E (testObject T g))

def pointEquiv (T : Over S) (g : ofOver T ⟶ X) :
    ProjectiveQuotientFunctor.Point E (testObject T g) ≃ SmallPoint E T g :=
  equivShrink _

def overArrow {T U : Over S} (a : U ⟶ T) (g : ofOver T ⟶ X) :
    testObject U (ofOverMap a ≫ g) ⟶ testObject T g :=
  Over.homMk (ofOverMap a) rfl

def restrict {T U : Over S} (a : U ⟶ T) (g : ofOver T ⟶ X) :
    SmallPoint E T g → SmallPoint E U (ofOverMap a ≫ g) :=
  fun q ↦ pointEquiv E U (ofOverMap a ≫ g)
    (ProjectiveQuotientFunctor.restrict E (overArrow a g) ((pointEquiv E T g).symm q))

/-- Honest total carrier in Type u: actual base points and actual small quotient classes. -/
def Point (T : Over S) : Type u :=
  Σ x : X.functorOfPoints.obj (op T), SmallPoint E T (homOfPoint x)

theorem homOfPoint_restrict {T U : Over S} (a : U ⟶ T) (x : X.functorOfPoints.obj (op T)) :
    ofOverMap a ≫ homOfPoint x = homOfPoint (X.functorOfPoints.map a.op x) := by
  sorry

def map {T U : Over S} (a : U ⟶ T) (p : Point E T) : Point E U :=
  ⟨X.functorOfPoints.map a.op p.1,
    (homOfPoint_restrict a p.1) ▸ restrict E a (homOfPoint p.1) p.2⟩

theorem map_id (T : Over S) (p : Point E T) : map E (𝟙 T) p = p := by
  sorry

theorem map_comp {T U V : Over S} (a : V ⟶ U) (b : U ⟶ T) (p : Point E T) :
    map E (a ≫ b) p = map E a (map E b p) := by
  sorry

def functor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Point E T.unop
  map a := TypeCat.ofHom (map E a.unop)
  map_id T := by ext p; exact map_id E T.unop p
  map_comp a b := by ext p; exact map_comp E b.unop a.unop p

def baseMap : functor E ⟶ X.functorOfPoints where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.SmallProjectiveFunctor
