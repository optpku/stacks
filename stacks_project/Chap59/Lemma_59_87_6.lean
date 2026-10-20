module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Connected

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

/- Lemma 59.87.6: if `f : X ⟶ S` is flat and every geometric point `x̄` of `X`
has geometrically connected fibres for the induced map of strict henselizations
`O_{S, f(x̄)}^{sh} ⟶ O_{X, x̄}^{sh}`, then for every cartesian square
with `g : T ⟶ S` quasi-compact and quasi-separated and every sheaf of sets
`F` on `T` étale, the comparison
`pullbackAlong f (pushforwardAlong g F) ⟶
  pushforwardAlong h (pullbackAlong e F)`
is an isomorphism, i.e. `f⁻¹ g_* F = h_* e⁻¹ F`. -/
@[stacks 0F00] #check
  (AlgebraicGeometry.Scheme.Etale.etaleSetBaseChange_of_geometricallyConnectedStrictHenselFibers :
    ∀ {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] [QuasiCompact g] [QuasiSeparated g]
    (h_cart : IsPullback h e f g)
    (h_fib : AlgebraicGeometry.Scheme.Etale.hasGeometricallyConnectedStrictHenselFibers f)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))),
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap f h e g h_cart F))
