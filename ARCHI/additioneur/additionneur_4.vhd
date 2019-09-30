----------------------------
-- Additionneur 4 bits
----------------------------

library ieee;
use ieee.std_logic_1164.all;

entity additionneur_4 is
  port (
    input_s : in std_logic;
    input_a : in std_logic_vector(3 downto 0);
    input_b : in std_logic_vector(3 downto 0);
    outputs : out std_logic_vector(3 downto 0);
    carry   : out std_logic
  );
end additionneur_4;


architecture additionneur_4_seq of additionneur_4 is
  component additionneur_1 
  port (
    input_s : in std_logic;
    input_a : in std_logic;
    input_b : in std_logic;
    outputs : out std_logic;
    carry   : out std_logic
    );
  end component;

  signal carry_A : std_logic;
  signal carry_B : std_logic;
  signal carry_C : std_logic;
  signal carry_D : std_logic;
begin

  add_1_A : additionneur_1 port map (
      input_s => input_s,
      input_a => input_a(0),
      input_b => input_b(0),
      outputs => outputs(0),
      carry   => carry_A
    );

  add_1_B : additionneur_1 port map (
      input_s => carry_A,
      input_a => input_a(1),
      input_b => input_b(1),
      outputs => outputs(1),
      carry   => carry_B
    );

  add_1_C : additionneur_1 port map (
      input_s => carry_B,
      input_a => input_a(2),
      input_b => input_b(2),
      outputs => outputs(2),
      carry   => carry_C
    );


  add_1_D : additionneur_1 port map (
      input_s => carry_C,
      input_a => input_a(3),
      input_b => input_b(3),
      outputs => outputs(3),
      carry   => carry_D
    );

    carry <= carry_D;

end additionneur_4_seq;