module

public import stacks_project.Chap78.Lemma_78_26_2_Square

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace
open scoped Bicategory

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 78.26.2: Assume `B → S` and `(U, R, s, t, c)` as in Definition 78.20.1 (1). Let
`G / U` be the stabilizer group algebraic space of the groupoid
`(U, R, s, t, c, e, i)`, see Definition 78.16.2. There is a canonical `2`-cartesian
diagram of stacks in groupoids on `(Sch/S)_fppf` with vertices `𝒮_G`, `𝒮_U`,
`I_{[U/R]}`, `[U/R]`, legs `𝒮_G ⟶ I_{[U/R]}` and `𝒮_G ⟶ 𝒮_U`, and cospan
`I_{[U/R]} ⟶ [U/R]` (forget) and `𝒮_U ⟶ [U/R]` (atlas). -/
@[stacks 06PC, instance]
instance inertiaCone_isBilimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (inertiaCone G).IsBilimit := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
