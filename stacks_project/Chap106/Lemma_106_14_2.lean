module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KeelMori.Separation
import StacksCheckRecall

/-!
# Quasi-separatedness and separatedness of Keel–Mori moduli spaces

If an algebraic stack has finite inertia and a uniform categorical moduli
space, then quasi-separatedness or separatedness of the stack passes to the
moduli algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 106.14.2 (1). Let `X` be an algebraic stack. Assume the inertia
morphism `forget X : I_X ⟶ X` is finite. Let `f : X ⟶ M.toGroupoids` be a
uniform categorical moduli space as constructed in Theorem 106.13.9. If `X`
is quasi-separated, then the algebraic space `M` is quasi-separated. -/
@[stacks 0DUY]
#check (AlgebraicGeometry.AlgebraicStack.isAbsolutelyQuasiSeparated_of_isUniformCategoricalModuliSpace :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f]
    [IsQuasiSeparated X], AlgebraicSpace.IsAbsolutelyQuasiSeparated M)

/- Lemma 106.14.2 (2). Let `X` be an algebraic stack. Assume the inertia
morphism `forget X : I_X ⟶ X` is finite. Let `f : X ⟶ M.toGroupoids` be a
uniform categorical moduli space as constructed in Theorem 106.13.9. If `X`
is separated, then the algebraic space `M` is separated. -/
@[stacks 0DUY]
#check (AlgebraicGeometry.AlgebraicStack.isAbsolutelySeparated_of_isUniformCategoricalModuliSpace :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids) [IsUniformCategoricalModuliSpace f]
    [IsSeparated X], AlgebraicSpace.IsAbsolutelySeparated M)

end AlgebraicGeometry.AlgebraicStack
