module

public import stacks_project.Chap85.Definition_85_12_1_Cartesian
import StacksCheckRecall

/-!
# Definition 85.12.1

In Situation 85.3.3, cartesianness of a sheaf of sets or abelian groups, an
`O`-module, an object of `D(C_total)`, or an object of `D(O)` on the total
simplicial site means that every simplex-operator comparison
`F(φ) : f_φ⁻¹ F_m ⟶ F_n` (respectively `f_φ^*` / `Lf_φ^*`) is an isomorphism.
-/

@[expose] public section

open CategoryTheory

/- Definition 85.12.1 (1)
In Situation 85.3.3, a sheaf `F` of sets or of abelian groups on `C_total` is
cartesian if the maps `F(φ) : f_φ⁻¹ F_m ⟶ F_n` are isomorphisms for all
`φ : m ⟶ n`. This is `Sheaf.IsCartesian`, specialized at `Type w` and at
`AddCommGrpCat.{w}`. -/
@[stacks 07TF] #check @SimplicialSites.Sheaf.IsCartesian
@[stacks 07TF] #check @SimplicialSites.IsCartesian
@[stacks 07TF] #check @SimplicialSites.Abelian.IsCartesian

/- Definition 85.12.1 (2)
In Situation 85.3.3, if `O` is a sheaf of rings on `C_total`, a sheaf `F` of
`O`-modules is cartesian if the maps `f_φ^* F_m ⟶ F_n` are isomorphisms for all
`φ : m ⟶ n`. -/
@[stacks 07TF] #check @SimplicialSites.Module.IsCartesian

/- Definition 85.12.1 (3)
In Situation 85.3.3, an object `K` of `D(C_total)` is cartesian if the maps
`f_φ⁻¹ K_m ⟶ K_n` are isomorphisms for all `φ : m ⟶ n`. -/
@[stacks 07TF] #check @SimplicialSites.AbelianDerived.IsCartesian
@[stacks 07TF] #check @SimplicialSites.Derived.IsCartesian

/- Definition 85.12.1 (4)
In Situation 85.3.3, if `O` is a sheaf of rings on `C_total`, an object `K` of
`D(O)` is cartesian if the maps `Lf_φ^* K_m ⟶ K_n` are isomorphisms for all
`φ : m ⟶ n`. -/
@[stacks 07TF] #check @SimplicialSites.ModuleDerived.IsCartesian
