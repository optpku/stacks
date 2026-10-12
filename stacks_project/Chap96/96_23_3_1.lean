/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.SpectralSequence.Presheaf
public import ReasLib.CategoryTheory.Sites.Cohomology.Terminal
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import Mathlib.CategoryTheory.Yoneda
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Presheaf.Cech

universe z w u

/- 96.23.3.1: on the associated τ-site of a category fibred in groupoids 𝒳,
if h_x ⟶ * is a locally surjective map of sheaves of sets, the sheafified
Čech levels h_{x,p} = sheafifiedLevel of the unique map
uliftYoneda.obj x ⟶ Presheaf.terminal are the sheafifications of the
(p+1)-fold products of the representable presheaf h_x, and every abelian
sheaf F admits a first-quadrant spectral sequence
E₁^{p,q} = H^q(h_{x,p}, F) ⇒ H^{p+q}(𝒳_τ, F). This is
exists_spectralSequence at K' = h_x and K = Presheaf.terminal; the abutment
H^{p+q}(*, F) is identified with global cohomology via isomorphicGlobal.
Local surjectivity of h_x ⟶ * is the load-bearing hypothesis (a smooth
surjective atlas supplies it geometrically, as in 06XH). -/
@[stacks 07AL]
#check
  fun {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology) (x : X.total)
      [HasSheafify (X.associatedTopology τ) (Type (max w u))]
      [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{max w u}]
      [HasExt.{z} (Sheaf (X.associatedTopology τ) AddCommGrpCat.{max w u})]
      [Presheaf.IsLocallySurjective (X.associatedTopology τ)
        ((Presheaf.terminalIsTerminal.{max w u} X.total).from
          (uliftYoneda.{max w u}.obj x))]
      (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{max w u}) ↦
    exists_spectralSequence
      ((Presheaf.terminalIsTerminal.{max w u} X.total).from
        (uliftYoneda.{max w u}.obj x)) F

/- The sheafified degree-p Čech level, i.e. the source object h_{x,p}. -/
#check @sheafifiedLevel

/- First-page target E₁^{p,q} = H^q(h_{x,p}, F), functorial in F. -/
#check @pageOneFunctor

/- Abutment target H^n(*, F), cohomology over the terminal presheaf. -/
#check @abutmentFunctor

/- Page-one identification (E.page 1).X (p, q) ≅ H^q(h_{x,p}, F). -/
#check @SpectralSequenceSystem.pageOneIso

/- Convergence of the spectral sequence to the terminal-presheaf abutment. -/
#check @SpectralSequenceSystem.converges_app

/- Identification of the terminal-presheaf abutment with global cohomology
H^n(𝒳_τ, F). -/
#check @Sheaf.TerminalCohomology.isomorphicGlobal

/- Čech nerve of an object over the terminal object, the product simplicial
object whose sheafification is h_{x,p}. -/
#check @cechNerveTerminalFrom

/- Identification of Arrow.mk (terminal.from X).cechNerve with
cechNerveTerminalFrom. -/
#check @CechNerveTerminalFrom.iso

/- The wide-cospan limit in each degree is the finite product ∏ h_x. -/
#check @CechNerveTerminalFrom.wideCospan.limitIsoPi
