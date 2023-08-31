import .tas
open Maude

infix (name := eq_kPid) ` ~ `:30 := bool.«~»₀
infix (name := eq_kLabel) ` ~ `:30 := bool.«~»₁
infix (name := eq_kStatus) ` ~ `:30 := bool.«~»₂

lemma enter_sort (s : kSys) (p : kPid) (h : (s.enter p) ⊳ MSort.Sys) :
  s ⊳ MSort.Sys ∧ p ⊳ MSort.Pid :=
begin
  cases h,
  case Maude.kSys.has_sort.subsort : s hs {
    cases s,
    all_goals {rw subsort at hs, contradiction},
  },
  case Maude.kSys.has_sort.enter_decl : _ _ hs hp {
    exact ⟨hs, hp⟩,
  },
end

lemma leave_sort (s : kSys) (p : kPid) (h : (s.leave p) ⊳ MSort.Sys) :
  s ⊳ MSort.Sys ∧ p ⊳ MSort.Pid :=
begin
  cases h,
  case Maude.kSys.has_sort.subsort : s hs {
    cases s,
    all_goals {rw subsort at hs, contradiction},
  },
  case Maude.kSys.has_sort.leave_decl : _ _ hs hp {
    exact ⟨hs, hp⟩,
  },
end

lemma mutex (S : kSys)(I J : kPid)
            (sort_S : S.has_sort MSort.Sys)
            (sort_I : I.has_sort MSort.Pid)
            (sort_J : J.has_sort MSort.Pid)
            (sys_ctor : S.ctor_only) :
 (((((kLabel.pc S I) ~ kLabel.cs) &&
    ((kLabel.pc S J) ~ kLabel.cs)) = tt
   →
   (I ~ J))) ∧
   (((kLabel.pc S I) ~ kLabel.cs) → (kStatus.lock S) ~ kStatus.close)
    :=
  begin
    induction S generalizing I J,
    --Maude.kSys.init
    case Maude.kSys.init{
      split,
      {
        simp,
        contradiction,
      },
      {
        simp,
        contradiction,
      },
    },
    case Maude.kSys.enter : s k{
      have apply_enter_sort := enter_sort _ _ sort_S,
      split,
      {
        cases eqes1 : bool.csubenter s k,
        case tt {
          simp[*],
          cases eqes2 : k ~ I,
          case tt {
            simp[*],
            cases eqes3 : k ~ J,
            case tt {
              -- intro eq_X_pid_trans,
              -- exact eq_X_pid_trans,
              -- simp[eqes3] at eq_X_pid_trans,
              -- rw bool.«~»₀_comm at eqes2,
              have eq_trans := bool.eq_X_pid_trans eqes3 eqes2,
              simp[*],
            },
            case ff {
              simp[*],
              cases eqes4 : kLabel.pc s J ~ kLabel.cs,
              case tt {
                simp[*],
                rw kSys.ctor_only at sys_ctor,
                specialize S_ih apply_enter_sort.left sys_ctor.left J I sort_J sort_I,
                have inst_right := S_ih.right,
                simp at eqes1,
                have inst_right_center := eqes1.right,
                simp[eqes4] at inst_right,
                specialize inst_right trivial,
                change (kStatus.lock s ~ kStatus.close) = tt at inst_right,
                rw bool.«~»₂_comm at inst_right,
                have eq_trans := bool.eq_status_trans inst_right inst_right_center,
                rw bool.«~»₂_comm at eq_trans,
                simp at eq_trans,
                contradiction,
              },
              case ff {
                simp[*],
                contradiction,
              },
            },
          },
          {
            cases eqes3 : k ~ J,
            case tt {
              cases eqes4 : kLabel.pc s I ~ kLabel.cs,
              case tt {
                simp[*],
                simp at eqes1,
                rw kSys.ctor_only at sys_ctor,
                specialize S_ih apply_enter_sort.left sys_ctor.left I J sort_I sort_J,
                have ih_right := S_ih.right,
                have eqes1_right := eqes1.right,
                simp[eqes4] at ih_right,
                specialize ih_right trivial,
                change (kStatus.lock s ~ kStatus.close) = tt at ih_right,
                rw bool.«~»₂_comm at ih_right,
                have eq_trans := bool.eq_status_trans ih_right eqes1_right,
                rw bool.«~»₂_comm at eq_trans,
                simp at eq_trans,
                contradiction,
              },
              case ff {
                simp[*],
                contradiction,
              },
            },
            case ff {
              simp[*],
              rw kSys.ctor_only at sys_ctor,
              specialize S_ih apply_enter_sort.left sys_ctor.left I J sort_I sort_J,
              have ih_right := S_ih.right,
              change (kLabel.pc s I ~ kLabel.cs) = tt → (kStatus.lock s ~ kStatus.close) = tt at ih_right,
              simp at eqes1,
              specialize ih_right,
              intro,
              have alfa_left := ᾰ.left,
              simp[alfa_left] at ih_right,
              specialize ih_right trivial,
              rw bool.«~»₂_comm at ih_right,
              have eqes1_right := eqes1.right,
              have eq_trans := bool.eq_status_trans ih_right eqes1_right,
              rw bool.«~»₂_comm at eq_trans,
              simp at eq_trans,
              contradiction,
            },
          },
        },
        case ff {
          simp[*],
          rw kSys.ctor_only at sys_ctor,
          specialize S_ih apply_enter_sort.left sys_ctor.left I J sort_I sort_J,
          simp at S_ih,
          exact S_ih.left,
        },
      },
      {
        cases eqes1 : bool.csubenter s k,
        case tt {
          simp[*],
        },
        case ff {
          simp[*],
          rw kSys.ctor_only at sys_ctor,
          specialize S_ih apply_enter_sort.left sys_ctor.left I J sort_I sort_J,
          change (kLabel.pc s I ~ kLabel.cs) = tt → (kStatus.lock s ~ kStatus.close) = tt,
          exact S_ih.right,
        },
      },
    },
    case Maude.kSys.leave : s k{
      have apply_leave_sort := leave_sort _ _ sort_S,
      split,
      {
        cases eqes1 : bool.csubleave s k,
        case tt {
          cases eqes2 : k ~ I,
          case tt {
            simp[*],
            contradiction,
          },
          case ff {
            cases eqes3 : k ~ J,
            case tt {
              simp[*],
              contradiction,
            },
            case ff {
              simp[*],
              rw kSys.ctor_only at sys_ctor,
              specialize S_ih apply_leave_sort.left sys_ctor.left I J sort_I sort_J,
              have inst_left := S_ih.left,
              simp[band_coe_iff] at inst_left,
              exact inst_left,
            },
          },
        },
        case ff {
          simp[*],
          rw kSys.ctor_only at sys_ctor,
          specialize S_ih apply_leave_sort.left sys_ctor.left I J sort_I sort_J,
          have inst_left := S_ih.left,
          simp[band_coe_iff] at inst_left,
          exact inst_left,
        },
      },
      {
        cases eqes1 :  bool.csubleave s k,
        case tt {
          cases eqes2 : k ~ I,
          case tt {
            simp[*],
            contradiction,
          },
          case ff {
            cases eqes3 : kLabel.pc s I ~ kLabel.cs,
            case tt {
              simp[eqes1,eqes2],
              rw kSys.ctor_only at sys_ctor,
              specialize S_ih apply_leave_sort.left sys_ctor.left I k sort_I apply_leave_sort.right,
              have inst_left := S_ih.left,
              rw bool.«~»₀_comm at eqes2,
              simp[*] at inst_left,
              simp at eqes1,
              rw bool.«~»₁_comm at eqes1,
              simp[*] at inst_left,
              specialize inst_left trivial,
              contradiction,
            },
            case ff {
              simp[*],
              contradiction,
            },
          },
        },
        case ff {
          simp[*],
          rw kSys.ctor_only at sys_ctor,
          specialize S_ih apply_leave_sort.left sys_ctor.left I J sort_I sort_J,
          exact S_ih.right,
        },
      },
    },
  end