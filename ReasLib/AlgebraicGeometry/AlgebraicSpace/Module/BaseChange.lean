module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

/-!
# The module base-change morphism of a commutative square

The comparison is the adjoint of the pulled-back counit. Its construction requires only
commutativity of the square; invertibility is a separate property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
variable {f : X ⟶ Y} {g : X' ⟶ Y'} {i : X' ⟶ X} {j : Y' ⟶ Y}

/-- The adjoint base-change map uses pullback composition and the actual original counit. -/
def baseChangeAdjoint (sq : i ≫ f = g ≫ j) (F : X.Modules) :
    (pullback g).obj ((pullback j).obj ((pushforward f).obj F)) ⟶
      (pullback i).obj F :=
  (pullbackCompIso g j).hom.app ((pushforward f).obj F) ≫
    eqToHom (congrArg (fun h : X' ⟶ Y ↦ (pullback h).obj ((pushforward f).obj F)) sq.symm) ≫
    (pullbackCompIso i f).inv.app ((pushforward f).obj F) ≫
    (pullback i).map ((pullbackPushforwardAdjunction f).counit.app F)

/-- The canonical module base-change comparison for a specified commutative square. -/
def baseChange (sq : i ≫ f = g ≫ j) :
    pushforward f ⋙ pullback j ⟶ pullback i ⋙ pushforward g where
  app F := (pullbackPushforwardAdjunction g).homEquiv _ _ (baseChangeAdjoint sq F)
  naturality := sorry

/-- The adjunction recovers the specified counit composite from the base-change morphism. -/
theorem baseChange_adjoint (sq : i ≫ f = g ≫ j) (F : X.Modules) :
    ((pullbackPushforwardAdjunction g).homEquiv _ _).symm ((baseChange sq).app F) =
      baseChangeAdjoint sq F :=
  Equiv.symm_apply_apply _ _

end AlgebraicGeometry.AlgebraicSpace.Modules
