module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian

/-!
# Noetherian algebraic stacks

The shared owners provide absolute quasi-separatedness, local Noetherianity,
and Noetherianity, together with their atlas and scheme-slice APIs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

#check (AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian.spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyNoetherian X],
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.IsLocallyNoetherian U.left)

#check (AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian.of :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicGeometry.IsLocallyNoetherian U.left],
    IsLocallyNoetherian X)

#check (AlgebraicGeometry.AlgebraicStack.instIsLocallyNoetherian_slice :
  ∀ {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left],
    IsLocallyNoetherian (GroupoidsOver.slice U))

#check (AlgebraicGeometry.AlgebraicStack.viewedOverSpecZ :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    GroupoidsOver (Spec (.of (ULift.{u} ℤ))))

#check (AlgebraicGeometry.AlgebraicStack.viewedOverSpecZ_p :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    (viewedOverSpecZ X).p = X.p ⋙ Over.map (specULiftZIsTerminal.from S))

#check (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

#check (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated.spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsQuasiSeparated X],
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)))

#check (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated.of :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)))
    (h_quasiSeparated :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))),
    IsQuasiSeparated X)

#check (AlgebraicGeometry.AlgebraicStack.instIsQuasiSeparated_slice :
  ∀ {S : Scheme.{u}} (U : Over S)
    [QuasiSeparatedSpace U.left],
    IsQuasiSeparated (GroupoidsOver.slice U))

#check (AlgebraicGeometry.AlgebraicStack.IsNoetherian :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

#check (AlgebraicGeometry.AlgebraicStack.IsNoetherian.spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsNoetherian X],
    IsQuasiCompact X ∧ IsQuasiSeparated X ∧ IsLocallyNoetherian X)

#check (AlgebraicGeometry.AlgebraicStack.IsNoetherian.of :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsQuasiCompact X] [IsQuasiSeparated X] [IsLocallyNoetherian X],
    IsNoetherian X)

#check (AlgebraicGeometry.AlgebraicStack.instIsNoetherian_slice :
  ∀ {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsNoetherian U.left],
    IsNoetherian (GroupoidsOver.slice U))

#check (AlgebraicGeometry.AlgebraicStack.isLocallyNoetherian_iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsLocallyNoetherian X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          AlgebraicGeometry.IsLocallyNoetherian U.left)

#check (AlgebraicGeometry.AlgebraicStack.isQuasiSeparated_iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsQuasiSeparated X ↔
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)) ∧
        Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated (Spec (.of (ULift.{u} ℤ))))
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)))

#check (AlgebraicGeometry.AlgebraicStack.isNoetherian_iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsNoetherian X ↔ IsQuasiCompact X ∧ IsQuasiSeparated X ∧ IsLocallyNoetherian X)

end AlgebraicGeometry.AlgebraicStack
