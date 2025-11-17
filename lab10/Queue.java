/*@

  predicate Cell (Cell c; Cell nxt, int v) =
    c.next |-> nxt &*& c.content |-> v;

  predicate lseg (Cell from, Cell to; list <int> l) =
    from == to ?
      l == nil :
      from != null &*& from.content |-> ?v &*&
      from.next |-> ?next &*& lseg(next, to, ?nvs) &*&
      l == cons (v, nvs);

  lemma void cell_null_lseg (Cell c)
    requires Cell(c, null, ?v);
    ensures lseg(c, null, cons(v, nil));
  {
    open Cell(c, null, v);
  }

  lemma void lseg_merge (Cell x, Cell y, Cell w)
    requires lseg(x, y, ?vs1) &*& lseg(y, w, ?vs2) &*& lseg(w, null, ?vs3);
    ensures lseg(x, w, append(vs1, vs2)) &*& lseg(w, null, vs3);
  {
    open lseg(w, null, vs3);
    open lseg(x, y, vs1);
    if (x != y) {
      lseg_merge(x.next, y, w);
    }
    else { }
  }

  lemma_auto void length_one (list<int> vs, int x)
    requires true;
    ensures length(vs) + 1 == length(append(vs, cons(x, nil)));
  {
    length_append(vs, cons(x, nil));
  }

@*/

class Cell
{
    Cell next;
    int content;

    public Cell (int v, Cell next)
    //@ requires true;
    //@ ensures true;
    {
        this.next = next;
        content = v;
    }
}

public class Queue
{
    Cell first;
    Cell last;
    int length;

    public Queue ()
    //@ requires true;
    //@ ensures true;
    {
        first = null;
        last = null;
        length = 0;
    }

    private void clear ()
    //@ requires true;
    //@ ensures true;
    {
        first = null;
        last = null;
        length = 0;
    }

    public void add (int x)
    //@ requires true;
    //@ ensures true;
    {
        Cell cell = new Cell(x, null);

        if (last == null) {
            last = cell;
            first = cell;
            length = 1;
        }
        else {
            if (last == first) {
                last.next = cell;
                last = cell;
                length = 2;
            }
            else {
                last.next = cell;
                last = cell;
                length = length + 1;
            }
        }
    }

    public boolean isEmpty ()
    //@ requires true;
    //@ ensures true;
    {
        return length == 0;
    }

    public int take ()
    //@ requires true;
    //@ ensures true;
    {
        if (first == last) {
            int c = first.content;
            this.clear();

            return c;
        }
        else {
            int c = first.content;
            length = length - 1;
            first = first.next;

            return c;
        }
    }
}

class Client
{
    public static void transfer (Queue q1, Queue q2)
    //@ requires true;
    //@ ensures true;
    {
        while (!q2.isEmpty())
        //@ invariant true;
        {
            int v = q2.take();
            q1.add(v);
        }
    }
}
