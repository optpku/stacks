module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Power
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.ProperSupport

/-!
# Proper-support completion on ideal-power thickenings

Completion on the closed subspace cut out by a positive ideal power uses the
inverse-image completion ideal and the composite structural morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Restricted proper-support completion on the closed subspace cut out by a
positive power of `K`, along the inverse-image ideal of `I`. -/
noncomputable def idealPowerCompletionFunctor (f : X ⟶ Y)
    (I K : IdealSubobject X)
    [IsNoetherian X] [LocallyOfFiniteType f]
    [IsQuasiCoherent I] [IsQuasiCoherent K] (e : ℕ+) :
    CoherentProperSupportOver (subschemeι (K ^ (e : ℕ)) ≫ f) ⥤
      CoherentFormalProperSupportOver (subschemeι (K ^ (e : ℕ)) ≫ f)
        (I.pullback (subschemeι (K ^ (e : ℕ)))) :=
  coherentProperSupportCompletionFunctor (subschemeι (K ^ (e : ℕ)) ≫ f)
    (I.pullback (subschemeι (K ^ (e : ℕ))))

/-- Restricted completion on the closed subspace cut out by `K ^ e` is
proper-support completion along the inverse image of `I` under its inclusion. -/
theorem idealPowerCompletionFunctor_eq (f : X ⟶ Y) (I K : IdealSubobject X)
    [IsNoetherian X] [LocallyOfFiniteType f]
    [IsQuasiCoherent I] [IsQuasiCoherent K] (e : ℕ+) :
    idealPowerCompletionFunctor f I K e =
      coherentProperSupportCompletionFunctor (subschemeι (K ^ (e : ℕ)) ≫ f)
        (I.pullback (subschemeι (K ^ (e : ℕ)))) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
