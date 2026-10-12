/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import StacksCheckRecall

/-!
# Lemma 17.9.3

Finite-type closure is an API of sheaves of modules on an arbitrary site, not
an artifact of the ringed-space presentation used in the source.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 17.9.3 (01B7) (1): the image of a morphism from a finite-type sheaf of modules is finite
type. This is the generic `SheafOfModules` image-closure theorem. -/
@[stacks 01B7 "(1)"]
#check fun {X : RingedSpace.{u}} {F G : X.Modules} (f : F ⟶ G) [F.IsFiniteType] ↦
  SheafOfModules.isFiniteType_image f

/- Lemma 17.9.3 (01B7) (2): the middle term of a short exact sequence is finite type when its
outer terms are finite type. This is the generic `SheafOfModules` extension-closure theorem. -/
@[stacks 01B7 "(2)"]
#check fun {X : RingedSpace.{u}} {F₁ F₂ F₃ : X.Modules}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (zero : f ≫ g = 0)
    (h : (ShortComplex.mk f g (zero := zero)).ShortExact)
    [F₁.IsFiniteType] [F₃.IsFiniteType] ↦
  SheafOfModules.isFiniteType_of_shortExact h
