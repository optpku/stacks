module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Functor

/-!
# Stability of elementary distinguished squares

Elementary distinguished squares of algebraic spaces are stable under restriction
to compatible open subspaces, pullback, and change of the base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare

/-- If `(U ⊂ W, f : V ⟶ W)` is an elementary distinguished square, `V' ⊂ V` and
`U ⊂ U' ⊂ W` are open subspaces, and `W' = U' ∪ f(V')`, then the restricted pair
`(U' ⊂ W', f' : V' ⟶ W')` is an elementary distinguished square. -/
theorem restrict {S : Scheme.{u}} {U V W U' V' W' : AlgebraicSpace S}
    {j : U ⟶ W} {f : V ⟶ W} [IsElementaryDistinguishedSquare j f]
    (jW' : U' ⟶ W) (iV' : V' ⟶ V) (iW' : W' ⟶ W) (j' : U' ⟶ W') (f' : V' ⟶ W')
    [IsOpenImmersion jW'] [IsOpenImmersion iV'] [IsOpenImmersion iW']
    (hU : ∃ k : U ⟶ U', k ≫ jW' = j)
    (hW' : Set.range (Points.map iW') =
      Set.range (Points.map jW') ∪ Set.range (Points.map (iV' ≫ f)))
    (hj' : j' ≫ iW' = jW') (hf' : f' ≫ iW' = iV' ≫ f) :
    IsElementaryDistinguishedSquare j' f' :=
  sorry

/-- The pullback of an elementary distinguished square of algebraic spaces along
any morphism `p : W' ⟶ W` is an elementary distinguished square. -/
theorem pullback {S : Scheme.{u}} {U V W W' : AlgebraicSpace S}
    (j : U ⟶ W) (f : V ⟶ W) (p : W' ⟶ W)
    [IsElementaryDistinguishedSquare j f] :
    IsElementaryDistinguishedSquare (Limits.pullback.snd j p)
      (Limits.pullback.snd f p) :=
  sorry

/-- Base change of an elementary distinguished square of algebraic spaces over `S`
along any scheme morphism `S' ⟶ S` is an elementary distinguished square. -/
theorem baseChange {S S' : Scheme.{u}} (g : S' ⟶ S) {U V W : AlgebraicSpace S}
    (j : U ⟶ W) (f : V ⟶ W) [IsElementaryDistinguishedSquare j f] :
    IsElementaryDistinguishedSquare (baseChangeMap g j) (baseChangeMap g f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
