----------------------------
-- Additionneur 1 bit
----------------------------

library ieee;
use ieee.std_logic_1164.all;

-- entitée additionneur 1 bit
entity additionneur_1 is
  port (
    input_s : in std_logic;
    input_a : in std_logic;
    input_b : in std_logic;
    outputs : out std_logic;
    carry   : out std_logic
  );
end;

-- architecture additionneur 1 bit
architecture additionneur_1_df of additionneur_1 is
begin
  outputs <= input_a xor input_b xor input_s;
  carry   <= (input_a and input_b) or (input_s and (input_a xor input_b));
end additionneur_1_df;



library ieee;
use ieee.std_logic_1164.all;

-- entitée pour le test
entity test_additionneur_1 is
end;

-- architecture pour le test
architecture test_additionneur_1_arc of test_additionneur_1 is
  component additionneur_1
  port (
    input_s : in std_logic;
    input_a : in std_logic;
    input_b : in std_logic;
    outputs : out std_logic;
    carry   : out std_logic
  );
  end component;

  signal input_s : std_logic;
  signal input_a : std_logic;
  signal input_b : std_logic;
  signal outputs : std_logic;
  signal carry   : std_logic;

begin
  -- instance de l'additionneur_1 a tester
  add_1 : additionneur_1 port map (
      -- mapping 1 pour 1
      input_s,
      input_a,
      input_b,
      outputs,
      carry
    );

  process
  begin
    input_s <= '0';

    input_a <= '0';
    input_b <= '0';
    wait for 5 ns;

    input_a <= '0';
    input_b <= '1';
    wait for 5 ns;

    input_a <= '1';
    input_b <= '1';
    wait for 5 ns;

    input_s <= '1';
    input_a <= '1';
    input_b <= '1';
    wait for 5 ns;

    wait;
  end process;

end test_additionneur_1_arc;