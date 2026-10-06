-- Merge default_prog into the table returned by your WezTerm configuration.
-- The chooser can attach to an existing session or create a new one.
-- Use linger's absolute path if it is not on the terminal's PATH.
return { default_prog = { 'linger', 'attach' } }
