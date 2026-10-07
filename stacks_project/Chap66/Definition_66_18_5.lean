module

public import stacks_project.Chap66.Lemma_66_18_6_Site
import StacksCheckRecall

@[expose] public section

/- Definition 66.18.5: let `S` be a scheme and let `X` be an algebraic space over `S`.
The site `X_affine,étale` of `X` is the Grothendieck topology `affineEtaleTopology X` on
the category `affineEtaleSite X` of étale morphisms `φ : ofOver U ⟶ X` with `U` an affine
scheme over `S` and `Etale φ` (morphisms `χ : U ⟶ U'` of schemes over `X` satisfy
`χ ≫ φ' = φ`). A family `{φ_i : (U_i ⟶ X) ⟶ (U ⟶ X)}` is a covering if and only if
`{U_i ⟶ U}` is a standard étale covering in the sense of `StandardEtaleCover` (Topologies,
Definition 34.4.5). Coverings are chosen as a `Small` set of such families, as in Sets
Lemma 3.11.1, generating `affineEtalePrecoverage` and then `affineEtaleTopology`. -/
@[stacks 0H01] #check AlgebraicGeometry.AlgebraicSpace.affineEtaleTopology
