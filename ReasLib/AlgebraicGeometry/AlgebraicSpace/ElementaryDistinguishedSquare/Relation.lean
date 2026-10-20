module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Diagonal

/-!
# Étale equivalence relation for an elementary distinguished square

The quotient algebraic space is defined by the étale equivalence
relation `R` on `U ⊔ V` whose five summands are `U`, `V'`, `V'`, `V`, and the
off-diagonal complement of `Δ_{V'/U}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare

variable {S : Scheme.{u}}

/-- The `Fin 2`-indexed family with values `U` and `V`. -/
def uvSummand (U V : AlgebraicSpace S) (i : Fin 2) : AlgebraicSpace S :=
  match i with
  | 0 => U
  | 1 => V

/-- The coproduct algebraic space `U ⊔ V`. -/
def uvCoproduct (U V : AlgebraicSpace S) : AlgebraicSpace S :=
  coproduct (uvSummand U V)

/-- The inclusion of `U` into `U ⊔ V`. -/
def uvιU (U V : AlgebraicSpace S) : U ⟶ uvCoproduct U V :=
  coproductι (uvSummand U V) 0

/-- The inclusion of `V` into `U ⊔ V`. -/
def uvιV (U V : AlgebraicSpace S) : V ⟶ uvCoproduct U V :=
  coproductι (uvSummand U V) 1

/-- The family of maps from the summands of `U ⊔ V` into `B`. -/
def uvHom {U V B : AlgebraicSpace S} (hU : U ⟶ B) (hV : V ⟶ B) :
    (i : Fin 2) → uvSummand U V i ⟶ B :=
  fun i ↦ match i with
    | 0 => hU
    | 1 => hV

/-- The morphism `U ⊔ V ⟶ B` induced by a pair of maps from the summands. -/
def uvDesc {U V B : AlgebraicSpace S} (hU : U ⟶ B) (hV : V ⟶ B) :
    uvCoproduct U V ⟶ B :=
  coproductDesc (uvHom hU hV)

/-- The open complement `V' ×_U V' \ Δ_{V'/U}` of the relative diagonal of a
separated morphism. -/
def offDiagonal {U V' : AlgebraicSpace S} (f' : V' ⟶ U) [Separated f'] :
    AlgebraicSpace S :=
  closedImmersionComplement (pullback.diagonal f')

/-- The inclusion of the off-diagonal complement into `V' ×_U V'`. -/
def offDiagonalι {U V' : AlgebraicSpace S} (f' : V' ⟶ U) [Separated f'] :
    offDiagonal f' ⟶ pullback f' f' :=
  closedImmersionComplementι (pullback.diagonal f')

/-- The off-diagonal algebraic space is the open complement of `Δ_{V'/U}`. -/
theorem offDiagonal_eq {U V' : AlgebraicSpace S} (f' : V' ⟶ U) [Separated f'] :
    offDiagonal f' =
      closedImmersionComplement (pullback.diagonal f') :=
  rfl

/-- The five-fold family `U`, `V'`, `V'`, `V`, `V' ×_U V' \ Δ_{V'/U}`. -/
def relationSummand {U V' : AlgebraicSpace S} (V : AlgebraicSpace S) (f' : V' ⟶ U)
    [Separated f'] (i : Fin 5) : AlgebraicSpace S :=
  match i with
  | 0 => U
  | 1 => V'
  | 2 => V'
  | 3 => V
  | 4 => offDiagonal f'

/-- The relation space `R = U ⊔ V' ⊔ V' ⊔ V ⊔ (V' ×_U V' \ Δ_{V'/U})`. -/
def relationSpace {U V' : AlgebraicSpace S} (V : AlgebraicSpace S) (f' : V' ⟶ U)
    [Separated f'] : AlgebraicSpace S :=
  coproduct (relationSummand V f')

/-- The five pair maps `R_i ⟶ (U ⊔ V) ×_S (U ⊔ V)` sending
`u, v', v', v, (v'₁, v'₂)` to `(u, u), (f'(v'), v'), (v', f'(v')), (v, v), (v'₁, v'₂)`. -/
def relationPair {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (i : Fin 5) :
    relationSummand V f' i ⟶ uvCoproduct U V ⨯ uvCoproduct U V :=
  match i with
  | 0 => prod.lift (uvιU U V) (uvιU U V)
  | 1 => prod.lift (f' ≫ uvιU U V) (ι ≫ uvιV U V)
  | 2 => prod.lift (ι ≫ uvιV U V) (f' ≫ uvιU U V)
  | 3 => prod.lift (uvιV U V) (uvιV U V)
  | 4 =>
    prod.lift (offDiagonalι f' ≫ pullback.fst f' f' ≫ ι ≫ uvιV U V)
      (offDiagonalι f' ≫ pullback.snd f' f' ≫ ι ≫ uvιV U V)

/-- The morphism `j : R ⟶ (U ⊔ V) ×_S (U ⊔ V)` of the étale equivalence relation. -/
def relationHom {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] : relationSpace V f' ⟶ uvCoproduct U V ⨯ uvCoproduct U V :=
  coproductDesc (relationPair ι f')

/-- On each summand, `relationHom` is the corresponding pair map. -/
theorem relationHom_spec {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (i : Fin 5) :
    coproductι (relationSummand V f') i ≫ relationHom ι f' = relationPair ι f' i :=
  sorry

/-- The first projection `t : R ⟶ U ⊔ V` of the relation. -/
def relationT {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] : relationSpace V f' ⟶ uvCoproduct U V :=
  relationHom ι f' ≫ prod.fst

/-- The second projection `s : R ⟶ U ⊔ V` of the relation. -/
def relationS {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] : relationSpace V f' ⟶ uvCoproduct U V :=
  relationHom ι f' ≫ prod.snd

end AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
