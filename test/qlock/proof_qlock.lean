import .qlock_bool
open Maude

lemma exit_sort (s : kSys) (p : kPid) (h : (s.exit p) ⊳ MSort.Sys) :
  s ⊳ MSort.Sys ∧ p ⊳ MSort.Pid :=
begin
  cases h,
  case Maude.kSys.has_sort.subsort : s hs {
    cases s, 
    all_goals {rw subsort at hs, contradiction},
  },
  case Maude.kSys.has_sort.exit_decl : _ _ hs hp {
    exact ⟨hs, hp⟩, 
  },
end

lemma want_sort (s : kSys) (p : kPid) (h : (s.want p) ⊳ MSort.Sys) :
  s ⊳ MSort.Sys ∧ p ⊳ MSort.Pid :=
begin
  cases h,
  case Maude.kSys.has_sort.subsort : s hs {
    cases s, 
    all_goals {rw subsort at hs, contradiction},
  },
  case Maude.kSys.has_sort.want_decl : _ _ hs hp {
    exact ⟨hs, hp⟩,
  },
end

lemma try_sort (s : kSys) (p : kPid) (h : (s.try p) ⊳ MSort.Sys) :
  s ⊳ MSort.Sys ∧ p ⊳ MSort.Pid :=
begin
  cases h,
  case Maude.kSys.has_sort.subsort : s hs {
    cases s, 
    all_goals {rw subsort at hs, contradiction},
  },
  case Maude.kSys.has_sort.try_decl : _ _ hs hp {
    exact ⟨hs, hp⟩, 
  },
end

lemma bar_sort (head : kPid) (tail : kQueue) (h : (kQueue.bar head tail) ⊳ MSort.Queue) :
  head ⊳ MSort.Pid ∧ tail ⊳ MSort.Queue :=
begin
  cases h,
  cases h_a,
  any_goals {rw subsort at h_ᾰ, contradiction},
  cases h_ᾰ_1,
  cases h_ᾰ_1_a,
  any_goals {rw subsort at h_ᾰ_1_ᾰ, contradiction},
  cases h_ᾰ_1,
  cases h_ᾰ_1_a,
  any_goals {rw subsort at h_ᾰ_1_ᾰ, contradiction},
  simp[*],
end

axiom eq1_trans (i j k : kPid) : bool.eq₁ i j → bool.eq₁ j k → bool.eq₁ i k 
axiom eq1_trans_congr (i j k : kPid) : bool.eq₁ i k → bool.eq₁ j k → bool.eq₁ i j 
axiom eq1_trans2 (i j k : kPid) : bool.eq₁ i j = tt → bool.eq₁ i k = tt → bool.eq₁ k j = tt
axiom eq_sort_trans (i j : kQueue) : i ⊳ MSort.Queue → i =E j → j ⊳ MSort.Queue
axiom kQueue_sc (q : kQueue) : q ⊳ MSort.Queue → ∃ c, q =E c ∧ c.ctor_only

lemma mutex (S : kSys)(I J : kPid) 
            (sort_S : S.has_sort Maude.MSort.Sys)
            (sort_I : I.has_sort Maude.MSort.Pid)
            (sort_J : J.has_sort Maude.MSort.Pid) :
 ((((bool.eq₀ (kLabel.pc S I) kLabel.cs) && (bool.eq₀ (kLabel.pc S J) kLabel.cs)) = tt
   → 
   (bool.eq₁ I J) = tt)) ∧
   ((bool.eq₀ (kLabel.pc S I) kLabel.cs) = tt → (bool.eq₁ (kPid.top (kQueue.queue S)) I) = tt)
    :=
  begin
   induction S generalizing I J,
   case Maude.kSys.init{
    split,
    {
      simp[kLabel.eqe.eq_pc₀ sort_I],
      intro useh1,
      have useh2 := kLabel.eqe.eq_pc₀ sort_I,
      simp[kLabel.eqe.eq_pc₀ sort_I] at useh2,
      contradiction,
    },
    {
      simp[kLabel.eqe.eq_pc₀ sort_I],
      intro useh1,
      have useh2 := kLabel.eqe.eq_pc₀ sort_I,
      simp[kLabel.eqe.eq_pc₀ sort_I] at useh2,
      contradiction,
    },
   },
   case Maude.kSys.exit : s k {
    have apply_exit_sort := exit_sort _ _ sort_S,
    split,
    {
    by_cases eqes1 :  bool.csubexit s k = tt,
    {
      have apply_eq := kLabel.eqe.eq_pc₃ apply_exit_sort.left apply_exit_sort.right sort_I eqes1,
      simp[apply_eq],
      by_cases eqes2 : (bool.eq₁ k I)  = tt,
      {
        simp[*,bool.eq_eq₀₂],
        contradiction,
      },
      {
        simp[*],
        by_cases eqes3 : (bool.eq₁ k J)  = tt,
        {
          simp[*,bool.eq_eq₀₂],
          contradiction,
        },
        {
          simp at eqes2,
          simp at eqes3,
          simp[*],
          intro eqes4,
          specialize S_x apply_exit_sort.left I J sort_I sort_J,
          simp[eqes4] at S_x,
          exact S_x.left trivial,
        },
      },
    },
    {
      have apply_eq2 := kSys.eqe.eq_exit apply_exit_sort.left apply_exit_sort.right, 
      simp[*],
      intro eqes2,
      simp at eqes1,
      simp[eqes1] at apply_eq2,
      simp[apply_eq2] at eqes2,
      specialize S_x apply_exit_sort.left I J sort_I sort_J,
      simp[eqes2] at S_x, 
      exact S_x.left trivial,
    },
    },
    {
      by_cases eqes1 : bool.eq₀ (kLabel.pc s k) kLabel.cs = tt,
      {
        have csubwanttrue : bool.csubexit s k = tt,
        {
          simp[*],
          rw bool.eq₀_comm,
          simp[*],
        },
        by_cases i_eq_k : (bool.eq₁ I k)  = tt,
        {
          simp[*],
          rw bool.eq₁_comm,
          simp[*],
          contradiction,
        },
        {
          simp at i_eq_k,
          by_cases eqes1 : bool.eq₀ (kLabel.pc s I) kLabel.cs = tt,
          {
            simp[*],
            contradiction,
          },
          {
            simp[*],
            rw bool.eq₁_comm,
            simp[*],
            contradiction,
          },
        },
      },
      {
        simp at eqes1,
        have csubwantfalse : bool.csubexit s k = ff,
        {
          simp[*],
          rw bool.eq₀_comm,
          simp[*],
        },
        simp[*],
        specialize S_x apply_exit_sort.left I J sort_I sort_J,
        exact S_x.right,
      },
    },
   },

   case Maude.kSys.try : s k {
    have apply_try_sort := try_sort _ _ sort_S,
    split,
    {
      by_cases eqes1 : bool.eq₀ (kLabel.pc s k) kLabel.ws = tt,
      {
        by_cases top_queue : bool.eq₁ (kPid.top (kQueue.queue s) ) k = tt,
        {
          have csubtrytrue : bool.csubtry s k = tt,
           {
            simp[*],
            split,
            {
             rw bool.eq₀_comm,
             simp[*],
            },
           {
            rw bool.eq₁_comm,
            simp[*],
           },
          },
          by_cases i_eq_k : (bool.eq₁ I k)  = tt,
          {
            by_cases j_eq_k : (bool.eq₁ J k)  = tt,
            {
              simp[*],
              rw bool.eq₁_comm,
              simp[*],
              rw bool.eq₁_comm,
              simp[*],
              rw bool.eq₁_comm at j_eq_k,
              have eq_trans := eq1_trans _ _ _  i_eq_k j_eq_k,
              intro,
              exact eq_trans,
            },
            {
              simp at j_eq_k,
              by_cases pc_cs : (bool.eq₀ (kLabel.pc s J) kLabel.cs) = tt,
              {
                rw bool.eq₁_comm,
                simp[*],
                rw bool.eq₁_comm at i_eq_k,
                simp[*],
                rw bool.eq₁_comm at j_eq_k,
                simp[*],
                specialize S_x apply_try_sort.left,
                have inst_right := (S_x J I sort_J sort_I).right,
                simp[pc_cs] at inst_right,
                specialize inst_right trivial,
                have tr := eq1_trans2 _ _ _ top_queue inst_right,
                rw bool.eq₁_comm at j_eq_k,
                simp[tr] at j_eq_k,
                contradiction,
              },
              {
                simp at pc_cs,
                simp[*],
                rw bool.eq₁_comm at i_eq_k,
                simp[*],
                rw bool.eq₁_comm at j_eq_k,
                simp[*],
                contradiction,
              },
            },
          },
          {
            simp at i_eq_k,
            by_cases j_eq_k : (bool.eq₁ J k)  = tt,
            {
              by_cases pc_cs : (bool.eq₀ (kLabel.pc s I) kLabel.cs) = tt,
              {
                simp[*],
                rw bool.eq₁_comm at i_eq_k,
                simp[*],
                rw bool.eq₁_comm at j_eq_k,
                simp[*],
                specialize S_x apply_try_sort.left,
                have inst_right := (S_x I J sort_I sort_J).right,
                simp[pc_cs] at inst_right,
                specialize inst_right trivial,
                have tr := eq1_trans2 _ _ _ top_queue inst_right,
                rw bool.eq₁_comm at i_eq_k,
                simp[tr] at i_eq_k,
                contradiction,
              },
              {
                simp at pc_cs,
                simp[*],
                rw bool.eq₁_comm at i_eq_k,
                simp[*],
                contradiction,
              },
            },
            {
              simp at j_eq_k,
              specialize S_x apply_try_sort.left I J sort_I sort_J,
              simp[*],
              rw bool.eq₁_comm at i_eq_k,
              simp[*],
              rw bool.eq₁_comm at j_eq_k,
              simp[*],
              simp[*] at S_x,
              exact S_x.left,
            },
          },
        },
        {
          simp at top_queue,
          have csubtryfalse : bool.csubtry s k = ff,
          {
            rw bool.eq₁_comm at top_queue,
            simp[*],
          },
          specialize S_x apply_try_sort.left I J sort_I sort_J,
          simp[*],
          simp[*] at S_x,
          exact S_x.left,
        },
      },
      {
        simp at eqes1,
        have csubtryfalse : bool.csubtry s k = ff,
        {
          rw bool.eq₀_comm at eqes1,
          simp[*],
        },
        specialize S_x apply_try_sort.left I J sort_I sort_J,
        simp[*],
        simp at S_x,
        exact S_x.left,
      },
    },
    --- invariant 2
    {
      specialize S_x apply_try_sort.left I J sort_I sort_J,
      by_cases eqes1 : bool.eq₀ (kLabel.pc s k) kLabel.ws = tt,
      {
        by_cases top_queue : bool.eq₁ (kPid.top (kQueue.queue s) ) k = tt,
        {
          have csubtrytrue : bool.csubtry s k = tt,
          {
            simp[*],
            split,
            {
              rw bool.eq₀_comm,
              simp[*],
            },
            {
              rw bool.eq₁_comm,
              simp[*],
            },
          },
          by_cases i_eq_k : (bool.eq₁ I k)  = tt,
          {
            simp[*],
            rw bool.eq₁_comm,
            simp[*],
            intro,
            have my_congr := eq1_trans_congr _ _ _ top_queue i_eq_k,
            exact my_congr,
          },
          {
            simp at i_eq_k,
            simp[*],
            rw bool.eq₁_comm,
            simp[*],
            exact S_x.right,
          },
        },
        {
          simp at top_queue,
          simp[*],
          have csubtryfalse : bool.csubtry s k = ff,
          {
            simp[*],
            rw bool.eq₁_comm,
            simp[*],
          },
          simp[*],
          exact S_x.right,
        },
      },
      {
        simp at eqes1,
        have csubtryfalse : bool.csubtry s k = ff,
        {
          simp[*],
          rw bool.eq₀_comm,
          simp[*],
        },
        simp[*],
        exact S_x.right,
      },
    },
   },

   case Maude.kSys.want : s k {
    have apply_want_sort := want_sort _ _ sort_S,
    split,
    {
    by_cases eqes1 : bool.csubwant s k = tt,
    {
      simp[*,kLabel.eqe.eq_pc₁],
      by_cases eqes2 : (bool.eq₁ k I)  = tt,
      {
        simp[*,bool.eq_eq₀₃],
        contradiction,
      },
      {
        simp at *,
        simp[*],
        by_cases eqes3 : (bool.eq₁ k J)  = tt,
        {
          simp[*,bool.eq_eq₀₃],
          contradiction,
        },
        {
          simp at eqes3,
          simp[*],
          specialize S_x apply_want_sort.left I J sort_I sort_J,
          exact S_x.left,
        },
      },
    },
    {
      simp at eqes1,
      simp[*],
      intro,
      simp[*],
    },
    },
    {
      specialize S_x apply_want_sort.left I J sort_I sort_J,
      by_cases eqes1 : bool.eq₀ (kLabel.pc s k) kLabel.rs = tt,
    {
        have csubwanttrue : bool.csubwant s k = tt,
        {
          simp[*],
          rw bool.eq₀_comm,
          simp[*],
        },
        by_cases i_eq_k : (bool.eq₁ k I)  = tt,
        {
          simp[*,bool.eq_eq₀₃],
          contradiction,
        },
        {
          simp at i_eq_k,
          simp[*,bool.eq_eq₀₃],
          have sort_Q := kQueue.has_sort.queue_decl apply_want_sort.left,
          cases (kQueue_sc (kQueue.queue s) (kQueue.has_sort.queue_decl apply_want_sort.left)) with q qh,
          cases q,

          case kQueue.empty {
            simp[*, qh.left],
            simp[bool.eq_eq₁₁, qh.left] at S_x,
            rw @ bool.eq₁_comm kPid.none I at S_x,
            have red_ff := bool.eq_eq₁₁ sort_I kPid.has_sort.none_decl,
            simp[red_ff] at S_x,
            exact S_x.right,
          },
          case kQueue.bar {
            simp[*, qh.left],
            have st := eq_sort_trans _ _ sort_Q qh.left,
            have args_sorts := bar_sort _ _ st,
            simp[*, qh.left] at S_x,
            simp[*],
            exact S_x.right,
          },

          all_goals {
            simp [kQueue.ctor_only,kQueue_sc] at *,
            contradiction,
          },
        },
      },
      {
        simp at eqes1,
        have csubwantfalse : bool.csubwant s k = ff,
        {
          simp[*],
          rw bool.eq₀_comm,
          exact eqes1,
        },
        simp[*],
        exact S_x.right,
      },
    },
   },
  end
