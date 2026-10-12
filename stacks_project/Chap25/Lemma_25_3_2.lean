/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Covering
import StacksCheckRecall

/-!
# Stability of covering formal-coproduct morphisms

The reusable covering-morphism property and its closure API are owned by
`ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Covering`.
-/

section

universe w v u

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (X : C)

/- Lemma 25.3.2, composition clause: ambient covering morphisms form a multiplicative
morphism property. -/
@[stacks 01G4 "composition"]
#check (inferInstance :
  (SemiRepresentableFamily.covering J :
    MorphismProperty (Limits.FormalCoproduct.{w} C)).IsMultiplicative)

/- Lemma 25.3.2, base-change stability clause for ambient covering morphisms. -/
@[stacks 01G4 "pullback stability"]
#check (inferInstance :
  (SemiRepresentableFamily.covering J :
    MorphismProperty (Limits.FormalCoproduct.{w} C)).IsStableUnderBaseChange)

/- Lemma 25.3.2, fixed-target composition clause: inverse image along the forgetful functor
preserves multiplicativity. -/
@[stacks 01G4 "fixed-target composition"]
#check (inferInstance :
  (SemiRepresentableFamily.OverFamily.covering J :
    MorphismProperty (SemiRepresentableFamily.OverFamily.{v, u, w} X)).IsMultiplicative)

/- Lemma 25.3.2, fixed-target base-change stability clause. -/
@[stacks 01G4 "fixed-target pullback stability"]
#check (inferInstance :
  (SemiRepresentableFamily.OverFamily.covering J :
    MorphismProperty
      (SemiRepresentableFamily.OverFamily.{v, u, w} X)).IsStableUnderBaseChange)

end

section

universe w v u

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : GrothendieckTopology C) (X : C)

/- Lemma 25.3.2, pullback-existence clause: every ambient covering morphism admits base
change along every morphism. -/
@[stacks 01G4 "pullback existence"]
#check (inferInstance :
  (SemiRepresentableFamily.covering J :
    MorphismProperty (Limits.FormalCoproduct.{w} C)).HasPullbacks)

/- Lemma 25.3.2, fixed-target pullback-existence clause. -/
@[stacks 01G4 "fixed-target pullback existence"]
#check (inferInstance :
  (SemiRepresentableFamily.OverFamily.covering J :
    MorphismProperty (SemiRepresentableFamily.OverFamily.{v, u, w} X)).HasPullbacks)

/- Lemma 25.3.2, fixed-target product clause, obtained from the generic base-change-stable
multiplicative morphism-property theorem. -/
@[stacks 01G4 "fixed-target binary products"]
#check (MorphismProperty.IsStableUnderBaseChange.prod_map
  (P := (SemiRepresentableFamily.OverFamily.covering J :
    MorphismProperty (SemiRepresentableFamily.OverFamily.{v, u, w} X))))

end

section

universe w v u

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)

/- Lemma 25.3.2, ambient product clause, obtained from the generic base-change-stable
multiplicative morphism-property theorem. -/
@[stacks 01G4 "binary products"]
#check (MorphismProperty.IsStableUnderBaseChange.prod_map
  (P := (SemiRepresentableFamily.covering J :
    MorphismProperty (Limits.FormalCoproduct.{w} C))))

end
