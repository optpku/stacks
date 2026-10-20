module

public import ReasLib.AlgebraicGeometry.Scheme.Lambda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Lambda

/-!
# Cardinal bounds for schemes and algebraic spaces

Typed checks expose the residue-field cardinal invariants and their specifications.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

namespace AlgebraicGeometry.Scheme

#check (AlgebraicGeometry.Scheme.lambda :
  ∀ (T : Scheme.{u}),
    Cardinal.{u})

#check (AlgebraicGeometry.Scheme.lambda_def :
  ∀ (T : Scheme.{u}),
    lambda T = ℵ₀ ⊔ ⨆ t : T, #(T.residueField t))

#check (AlgebraicGeometry.Scheme.aleph0_le_lambda :
  ∀ (T : Scheme.{u}),
    ℵ₀ ≤ lambda T)

#check (AlgebraicGeometry.Scheme.cardinalMk_residueField_le_lambda :
  ∀ (T : Scheme.{u}) (t : T),
    #(T.residueField t) ≤ lambda T)

#check (AlgebraicGeometry.Scheme.lambda_le_size :
  ∀ (T : Scheme.{u}),
    lambda T ≤ T.size)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.lambda :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Cardinal.{u})

#check (AlgebraicGeometry.AlgebraicSpace.lambda_spec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : ofOver U ⟶ X) [Etale p] (hp : Function.Surjective (Points.map p)),
    lambda X = Scheme.lambda U.left)

#check (AlgebraicGeometry.AlgebraicSpace.lambda_ofOver :
  ∀ {S : Scheme.{u}} (U : Over S),
    lambda (ofOver U) = Scheme.lambda U.left)

end AlgebraicGeometry.AlgebraicSpace
