module

public import ReasLib.Topology.Presheaf.Cech.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace TopCat.Presheaf

universe u uι

/- Definition 20.9.1 (1): for a topological space `X`, an indexed open family
`𝒰 : ι → Opens X` (Stacks covering notation `𝒰 : U = ⋃ᵢ Uᵢ` is recovered later by
`U = iSup 𝒰` when needed), and an abelian presheaf `F`, the Čech complex
Čech•(𝒰, F) is `cechComplex 𝒰 F`. -/
@[stacks 01EF]
#check (TopCat.Presheaf.cechComplex :
  {X : TopCat.{u}} → {ι : Type uι} → (ι → Opens X) →
    X.Presheaf AddCommGrpCat.{max u uι} → CochainComplex AddCommGrpCat.{max u uι} ℕ)

/- Definition 20.9.1 (2): the Čech cohomology groups Čech Hⁱ(𝒰, F) are the homology
groups `Hⁱ(Čech•(𝒰, F))` of that complex, i.e. `cechCohomology 𝒰 F i`. -/
@[stacks 01EF]
#check (TopCat.Presheaf.cechCohomology :
  {X : TopCat.{u}} → {ι : Type uι} → (ι → Opens X) →
    X.Presheaf AddCommGrpCat.{max u uι} → ℕ → AddCommGrpCat.{max u uι})

/- Identification `Hⁱ(Čech•(𝒰, F)) = Čech Hⁱ(𝒰, F)`. -/
@[stacks 01EF]
#check (TopCat.Presheaf.cechComplex_homology :
  ∀ {X : TopCat.{u}} {ι : Type uι} (U : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u uι}) (i : ℕ),
    (cechComplex U F).homology i = cechCohomology U F i)
