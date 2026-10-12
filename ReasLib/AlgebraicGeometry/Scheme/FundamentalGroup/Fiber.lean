/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisAction
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.PreGaloisCategory
open CategoryTheory.Functor
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- The set-valued finite étale fiber is the actual functor of lifts of the
separably closed point, expressed in the slice category. -/
def finiteEtaleFiberType (s : Spec (.of Ω) ⟶ X) : FiniteEtale X ⥤ Type u :=
  MorphismProperty.Over.forget finiteEtaleMorphism ⊤ X ⋙ coyoneda.obj (op (Over.mk s))

/-- A finite étale scheme has a finite fiber at a separably closed point. -/
instance finiteEtaleFiberType_finite (s : Spec (.of Ω) ⟶ X) (V : FiniteEtale X) :
    Finite ((finiteEtaleFiberType s).obj V) := sorry

/-- The finite-set fiber functor retains the actual scheme-valued lifts. -/
def finiteEtaleFiberAt [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) : FiniteEtale X ⥤ FintypeCat.{u} where
  obj V := FintypeCat.of ((finiteEtaleFiberType s).obj V)
  map a := FintypeCat.homMk ((finiteEtaleFiberType s).map a)
  map_id := sorry
  map_comp := sorry

/-- The étale fundamental group is the automorphism group of the actual
finite étale fiber functor, with its canonical profinite topology. -/
abbrev fundamentalGroup [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) := Aut (finiteEtaleFiberAt s)

/-- Base change identifies geometric lifts through the actual slice
map/pullback adjunction, not through equality of the two fiber functors. -/
def finiteEtaleFiberBaseChangeEquiv (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)
    (V : FiniteEtale Y) :
    (finiteEtaleFiberType s).obj ((finiteEtaleBaseChange f).obj V) ≃
      (finiteEtaleFiberType (s ≫ f)).obj V :=
  ((Over.mapPullbackAdj f).homEquiv (Over.mk s) (Over.mk V.hom)).symm

/-- The finite étale base-change comparison has the explicit adjunction
equivalence on each geometric fiber. -/
def finiteEtaleFiberBaseChangeIso [IsSepClosed Ω] (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X) :
    finiteEtaleBaseChange f ⋙ finiteEtaleFiberAt s ≅ finiteEtaleFiberAt (s ≫ f) :=
  NatIso.ofComponents (fun V ↦
    { hom := FintypeCat.homMk (finiteEtaleFiberBaseChangeEquiv f s V)
      inv := FintypeCat.homMk (finiteEtaleFiberBaseChangeEquiv f s V).symm
      hom_inv_id := sorry
      inv_hom_id := sorry }) (fun _ ↦ sorry)

namespace Hom

/-- A scheme morphism induces a fundamental-group homomorphism by
whiskering with finite étale base change and the specified fiber comparison. -/
def fundamentalGroupMap [IsSepClosed Ω] (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X) :
    ContinuousMonoidHom (Scheme.fundamentalGroup s) (Scheme.fundamentalGroup (s ≫ f)) where
  toFun a := (finiteEtaleFiberBaseChangeIso f s).conjAut
    (((whiskeringLeft (FiniteEtale Y) (FiniteEtale X) FintypeCat).obj
      (finiteEtaleBaseChange f)).mapAut (finiteEtaleFiberAt s) a)
  map_one' := sorry
  map_mul' := sorry
  continuous_toFun := sorry

/-- The induced homomorphism is the conjugate of the actual whiskered
automorphism under the specified geometric fiber comparison. -/
theorem fundamentalGroupMap_apply [IsSepClosed Ω] (f : X ⟶ Y) (s : Spec (.of Ω) ⟶ X)
    (a : Scheme.fundamentalGroup s) :
    fundamentalGroupMap f s a = (finiteEtaleFiberBaseChangeIso f s).conjAut
      (((whiskeringLeft (FiniteEtale Y) (FiniteEtale X) FintypeCat).obj
        (finiteEtaleBaseChange f)).mapAut (finiteEtaleFiberAt s) a) := rfl

end Hom
end AlgebraicGeometry.Scheme
