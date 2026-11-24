import MyProject.Theta.Core

namespace WCT

/-- Open nontriviality obligation for a specified model. -/
def NontrivialTheta {S : Type} (M : ThetaModel S) (p : ThetaParams) : Prop :=
  ∃ s : S, M.step p s ≠ s

theorem Theta_deterministic {S : Type} (M : ThetaModel S)
    (p : ThetaParams) (s1 s2 : S) (h : s1 = s2) :
    M.step p s1 = M.step p s2 :=
  congrArg (M.step p) h

/-- Failure of additivity or real homogeneity, not failure of injectivity. -/
def NonlinearTheta {S : Type} [AddCommMonoid S] [Module ℝ S]
    (M : ThetaModel S) (p : ThetaParams) : Prop :=
  ¬ ((∀ x y : S, M.step p (x + y) = M.step p x + M.step p y) ∧
     (∀ (c : ℝ) (x : S), M.step p (c • x) = c • M.step p x))

def AttractorExists {S : Type} [MetricSpace S]
    (M : ThetaModel S) (p : ThetaParams) : Prop :=
  ∃ s : S, IsAttractor (M.step p) s

def AttractorUnique {S : Type} [MetricSpace S]
    (M : ThetaModel S) (p : ThetaParams) : Prop :=
  ∀ s1 s2 : S, IsAttractor (M.step p) s1 →
    IsAttractor (M.step p) s2 → s1 = s2

end WCT
